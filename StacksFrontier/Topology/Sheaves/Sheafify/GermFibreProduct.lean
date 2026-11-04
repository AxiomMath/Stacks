module

public import Mathlib.CategoryTheory.ConcreteCategory.ReflectsIso
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.Topology.Sheaves.Sheafify

/-!
# Sheafification as a fibre product of germ data (Stacks 0084)

Let `X` be a topological space and `F` a presheaf of sets on `X`. Attached to `F` there is the
*product presheaf* `piPresheaf F`, whose sections over an open `U` are the arbitrary families
`(σ x)_{x ∈ U}` with `σ x` a germ in the stalk `F.stalk x`, restriction being reindexing along the
inclusion of the smaller open. Sending a section of `F` to the family of its germs is a morphism of
presheaves `toPiPresheaf F : F ⟶ piPresheaf F`.

The sheafification `F.sheafify` is realised in Mathlib as the subsheaf of `piPresheaf F` cut out by
the local-germ predicate, and its stalks agree with those of `F` (`sheafifyStalkIso`). Under that
identification a section of `F.sheafify` over `U` has two natural images:

* `sheafifyGerms F U`, its family of germs, living in `∀ x : U, F.stalk x`, which is at the same
  time a section of `piPresheaf F` over `U` (the two types are definitionally equal — this is the
  source's identification `Π(F)(U) = ∏_{x ∈ U} F_x`, and it is why the two horizontal legs `a` and
  `b` of the source's square are one and the same function here);
* the further germs of that family, either taken inside `piPresheaf F` (`piPresheafGerms`) or
  obtained by pushing germs of `F` forward along `toPiPresheaf F` (`piPresheafStalkMap`).

The content of the tag is that the resulting square commutes
(`piPresheafGerms_comp_sheafifyGerms`) and is a fibre product of sets: the canonical map from
`F.sheafify` over `U` into `PullbackSections F U`, the set-theoretic fibre product of
`piPresheafGerms` and `piPresheafStalkMap`, is a bijection (`bijective_canonicalToPullback`).

Because the ambient category is `Type u`, the fibre product is taken as a plain subtype of a
product rather than through `CategoryTheory.Limits.pullback`; this keeps the bijection statement
elementary and matches the source, which asserts a fibre-product diagram *of sets*. The
identification of the two stalks is packaged as `stalkSheafifyEquiv`, a bijection obtained from the
fact that `toSheafify` induces a bijection on stalks (`stalk_sheafify_bijective`, Stacks 007X).
-/

@[expose] public section

open CategoryTheory Opposite TopologicalSpace

universe u

namespace TopCat.Presheaf

variable {X : TopCat.{u}}

/-- **Stacks 0084.** The product presheaf `Π(F)`: its sections over an open `U` are the families
`(σ x)_{x ∈ U}` of germs `σ x : F.stalk x`, with restriction along `V ≤ U` given by projecting onto
the factors indexed by the points of `V`. -/
@[stacks 0084, implicit_reducible]
noncomputable def piPresheaf (F : Presheaf (Type u) X) : Presheaf (Type u) X where
  obj U := ∀ x : U.unop, F.stalk x.val
  map {U V} i := ↾fun (s : ∀ x : U.unop, F.stalk x.val) (y : V.unop) =>
    s ⟨y.val, (leOfHom i.unop) y.property⟩
  map_id _ := rfl
  map_comp _ _ := rfl

/-- Restriction in `piPresheaf F` along `V ≤ U` evaluates a family at the points of `V`. -/
@[simp]
lemma piPresheaf_map_apply (F : Presheaf (Type u) X) {U V : (Opens X)ᵒᵖ} (i : U ⟶ V)
    (s : (piPresheaf F).obj U) (y : V.unop) :
    (piPresheaf F).map i s y = s ⟨y.val, (leOfHom i.unop) y.property⟩ := rfl

/-- **Stacks 0084.** The canonical morphism of presheaves `F ⟶ Π(F)` sending a section
`s ∈ F(U)` to the family `(s_x)_{x ∈ U}` of its germs. -/
@[stacks 0084]
noncomputable def toPiPresheaf (F : Presheaf (Type u) X) : F ⟶ piPresheaf F where
  app U := ↾fun (s : F.obj U) (x : U.unop) =>
    F.germ U.unop x.val x.property s
  naturality U V i := by
    ext s
    funext y
    simp only [TypeCat.Fun.toFun_apply, ConcreteCategory.comp_apply, TypeCat.ofHom_apply,
      piPresheaf_map_apply]
    exact F.germ_res_apply i.unop y.val y.property s

/-- The `x`-component of the image of `s` under `toPiPresheaf F` is the germ of `s` at `x`. -/
@[simp]
lemma toPiPresheaf_app_apply (F : Presheaf (Type u) X) (U : (Opens X)ᵒᵖ) (s : F.obj U)
    (x : U.unop) : (toPiPresheaf F).app U s x = F.germ U.unop x.val x.property s := rfl

/-- `stalkToFiber` is a left inverse of the stalk map induced by `toSheafify`. -/
private lemma stalkToFiber_stalkFunctor_map_toSheafify (F : Presheaf (Type u) X) (x : X)
    (a : F.stalk x) : F.stalkToFiber x ((stalkFunctor (Type u) x).map F.toSheafify a) = a := by
  obtain ⟨U, hx, s, rfl⟩ := F.exists_germ_eq a
  rw [stalkFunctor_map_germ_apply (F := F) U x hx F.toSheafify s]
  exact stalkToFiber_germ (Sheafify.isLocallyGerm F) U x hx
    (ConcreteCategory.hom (F.toSheafify.app (op U)) s)

/-- The map on stalks `F.stalk x → F.sheafify.presheaf.stalk x` induced by the sheafification
morphism `F.toSheafify` is bijective; this is Stacks 007X. -/
theorem stalk_sheafify_bijective (F : Presheaf (Type u) X) (x : X) :
    Function.Bijective ((stalkFunctor (Type u) x).map F.toSheafify) := by
  have h_bij : Function.Bijective (F.stalkToFiber x) :=
    (sheafifyStalkIso F x).toEquiv.bijective
  constructor
  · exact Function.HasLeftInverse.injective
      ⟨_, stalkToFiber_stalkFunctor_map_toSheafify F x⟩
  · intro y
    exact ⟨F.stalkToFiber x y, h_bij.1 (stalkToFiber_stalkFunctor_map_toSheafify F x _)⟩

/-- The canonical bijection `F.stalk x ≃ F.sheafify.presheaf.stalk x` between the stalk of `F` and
the stalk of its sheafification, induced by `F.toSheafify`. -/
noncomputable def stalkSheafifyEquiv (F : Presheaf (Type u) X) (x : X) :
    F.stalk x ≃ F.sheafify.presheaf.stalk x :=
  Equiv.ofBijective _ (stalk_sheafify_bijective F x)

/-- The family of germs of a section of the sheafification: germs are taken in `F.sheafify` at each
point of `U` and transported back along the identification
`F.sheafify.presheaf.stalk x = F.stalk x`. Since `(piPresheaf F).obj (op U)` is by definition
`∀ x : U, F.stalk x`, this single function is both of the two maps out of
`F.sheafify.presheaf.obj (op U)` appearing in the source's square. -/
noncomputable def sheafifyGerms (F : Presheaf (Type u) X) (U : Opens X) :
    F.sheafify.presheaf.obj (op U) → ∀ x : U, F.stalk x.val :=
  fun s x => (stalkSheafifyEquiv F x.val).symm
    (F.sheafify.presheaf.germ U x.val x.property s)

/-- The family of germs of a section of `Π(F)`: its `x`-component is the germ map of the presheaf
`Π(F)` at the point `x`. -/
noncomputable def piPresheafGerms (F : Presheaf (Type u) X) (U : Opens X) :
    (piPresheaf F).obj (op U) → ∀ x : U, (piPresheaf F).stalk x.val :=
  fun s x => (piPresheaf F).germ U x.val x.property s

/-- The map on families of germs induced by `toPiPresheaf F`: its `x`-component is the stalk map at
`x` of the morphism of presheaves `F ⟶ Π(F)`. -/
noncomputable def piPresheafStalkMap (F : Presheaf (Type u) X) (U : Opens X) :
    (∀ x : U, F.stalk x.val) → ∀ x : U, (piPresheaf F).stalk x.val :=
  fun σ x => (stalkFunctor (Type u) x.val).map (toPiPresheaf F) (σ x)

/-- The set-theoretic fibre product of `piPresheafGerms` and `piPresheafStalkMap`, i.e. the corner
`Π(F)(U) ×_{∏_x Π(F)_x} ∏_x F_x` of the source's square. -/
def PullbackSections (F : Presheaf (Type u) X) (U : Opens X) : Type u :=
  { p : (piPresheaf F).obj (op U) × (∀ x : U, F.stalk x.val) //
    piPresheafGerms F U p.1 = piPresheafStalkMap F U p.2 }

/-- `stalkSheafifyEquiv` is by construction the stalk map induced by `toSheafify`. -/
private lemma stalkSheafifyEquiv_apply (F : Presheaf (Type u) X) (x : X) (a : F.stalk x) :
    (stalkSheafifyEquiv F x) a = (stalkFunctor (Type u) x).map F.toSheafify a := by
  simp [stalkSheafifyEquiv, Equiv.ofBijective_apply]

/-- `stalkSheafifyEquiv` sends the germ of `t` to the germ of its image in `F.sheafify`. -/
private lemma stalkSheafifyEquiv_germ (F : Presheaf (Type u) X) {x : X} {V : Opens X}
    (hxV : x ∈ V) (t : F.obj (op V)) :
    stalkSheafifyEquiv F x (F.germ V x hxV t) =
      F.sheafify.presheaf.germ V x hxV (F.toSheafify.app (op V) t) := by
  rw [stalkSheafifyEquiv_apply]
  exact stalkFunctor_map_germ_apply (F := F) V x hxV F.toSheafify t

/-- Pushing the germ of `t` forward along `toPiPresheaf F` gives the germ of its image in
`Π(F)`. -/
private lemma stalkFunctor_map_toPiPresheaf_of_germ_eq (F : Presheaf (Type u) X) {x : X}
    {V : Opens X} (hxV : x ∈ V) (t : F.obj (op V)) {a : F.stalk x} (ht : F.germ V x hxV t = a) :
    (stalkFunctor (Type u) x).map (toPiPresheaf F) a =
      (piPresheaf F).germ V x hxV ((toPiPresheaf F).app (op V) t) := by
  rw [← ht]
  exact stalkFunctor_map_germ_apply (F := F) V x hxV (toPiPresheaf F) t

/-- **Stacks 0084.** The square commutes: taking germs of a section of `F.sheafify` and then germs
inside `Π(F)` agrees with taking germs and then pushing them forward along `F ⟶ Π(F)`. -/
@[stacks 0084]
theorem piPresheafGerms_comp_sheafifyGerms (F : Presheaf (Type u) X) (U : Opens X) :
    piPresheafGerms F U ∘ sheafifyGerms F U = piPresheafStalkMap F U ∘ sheafifyGerms F U := by
  funext s x
  simp only [Function.comp_apply, piPresheafStalkMap, sheafifyGerms]
  set elem := (stalkSheafifyEquiv F x.val).symm (F.sheafify.presheaf.germ U x.val x.property s)
  obtain ⟨V, hxV, t, ht⟩ := F.exists_germ_eq elem
  have ht' : F.germ V x.val hxV t = elem := ht
  rw [stalkFunctor_map_toPiPresheaf_of_germ_eq F hxV t ht']
  have hsheaf_germ_eq : F.sheafify.presheaf.germ V x.val hxV (F.toSheafify.app (op V) t) =
      F.sheafify.presheaf.germ U x.val x.property s := by
    rw [← stalkSheafifyEquiv_germ, ht', Equiv.apply_symm_apply]
  obtain ⟨W, hxW, hWV, hWU, heq_res⟩ := F.sheafify.presheaf.germ_eq x.val hxV x.property
    (F.toSheafify.app (op V) t) s hsheaf_germ_eq
  have sect_eq : (piPresheaf F).map hWU.op (sheafifyGerms F U s) =
      (piPresheaf F).map hWV.op ((toPiPresheaf F).app (op V) t) := by
    funext y
    simp only [piPresheaf_map_apply, toPiPresheaf_app_apply, sheafifyGerms]
    apply (stalkSheafifyEquiv F y.val).injective
    rw [Equiv.apply_symm_apply, stalkSheafifyEquiv_germ, ← germ_res_apply _ hWU y.val y.property,
      ← germ_res_apply _ hWV y.val y.property, heq_res]
  calc (piPresheaf F).germ U x.val x.property (sheafifyGerms F U s)
      = (piPresheaf F).germ W x.val hxW ((piPresheaf F).map hWU.op (sheafifyGerms F U s)) :=
        (germ_res_apply (piPresheaf F) hWU x.val hxW (sheafifyGerms F U s)).symm
    _ = (piPresheaf F).germ W x.val hxW
          ((piPresheaf F).map hWV.op ((toPiPresheaf F).app (op V) t)) :=
        congrArg ((piPresheaf F).germ W x.val hxW) sect_eq
    _ = (piPresheaf F).germ V x.val hxV ((toPiPresheaf F).app (op V) t) :=
        germ_res_apply (piPresheaf F) hWV x.val hxW ((toPiPresheaf F).app (op V) t)

/-- The canonical map from `F.sheafify.presheaf.obj (op U)` into the set-theoretic fibre product,
whose two components are both given by `sheafifyGerms`. -/
noncomputable def canonicalToPullback (F : Presheaf (Type u) X) (U : Opens X) :
    F.sheafify.presheaf.obj (op U) → PullbackSections F U :=
  fun s => ⟨(sheafifyGerms F U s, sheafifyGerms F U s),
    congrFun (piPresheafGerms_comp_sheafifyGerms F U) s⟩

/-- If `τ` and `σ` have equal germs in `Π(F)`, then near each point `x` the germ `σ x` is presented
by a section `t` of `F` whose image in `Π(F)` agrees with `τ` on a smaller neighbourhood. -/
private lemma exists_res_eq_of_piPresheafGerms_eq (F : Presheaf (Type u) X) (U : Opens X)
    (τ : (piPresheaf F).obj (op U)) (σ : ∀ x : U, F.stalk x.val)
    (h : piPresheafGerms F U τ = piPresheafStalkMap F U σ) (x : U) :
    ∃ (V : Opens X) (hxV : x.val ∈ V) (t : F.obj (op V)) (W : Opens X) (_hxW : x.val ∈ W)
      (hWU : W ⟶ U) (hWV : W ⟶ V), F.germ V x.val hxV t = σ x ∧
        (piPresheaf F).map hWU.op τ =
          (piPresheaf F).map hWV.op ((toPiPresheaf F).app (op V) t) := by
  obtain ⟨V, hxV, t, ht⟩ := F.exists_germ_eq (σ x)
  obtain ⟨W, hxW, hWU, hWV, heq_res⟩ := (piPresheaf F).germ_eq x.val x.property hxV τ
    ((toPiPresheaf F).app (op V) t)
    ((congr_fun h x).trans (stalkFunctor_map_toPiPresheaf_of_germ_eq F hxV t ht))
  exact ⟨V, hxV, t, W, hxW, hWU, hWV, ht, heq_res⟩

/-- An element of the fibre product has equal components: the germ family in `Π(F)(U)` and the germ
family in `∏_{x ∈ U} F_x` coincide. This is the source's identification `Π(F)(U) = ∏_x F_x` seen
through the square. -/
private lemma pullback_fst_eq_snd (F : Presheaf (Type u) X) (U : Opens X)
    (τ : (piPresheaf F).obj (op U)) (σ : ∀ x : U, F.stalk x.val)
    (h : piPresheafGerms F U τ = piPresheafStalkMap F U σ) : τ = σ := by
  funext x
  obtain ⟨V, hxV, t, W, hxW, hWU, hWV, ht, heq_res⟩ :=
    exists_res_eq_of_piPresheafGerms_eq F U τ σ h x
  have := congr_fun heq_res ⟨x.val, hxW⟩
  simpa [← ht] using this

/-- Sections of the sheafification are determined by their germs: this is the separation half of
the sheaf axiom for `F.sheafify`. -/
private lemma sheafifyGerms_injective (F : Presheaf (Type u) X) (U : Opens X) :
    Function.Injective (sheafifyGerms F U) := by
  intro s₁ s₂ h
  apply section_ext F.sheafify U
  intro x hx
  have hx_eq := congr_fun h ⟨x, hx⟩
  simp only [sheafifyGerms] at hx_eq
  exact (stalkSheafifyEquiv F x).symm.injective.eq_iff.mp hx_eq

/-- The germ family of the section of `F.sheafify` presented by a locally-germ family `τ` is `τ`
itself. -/
private lemma sheafifyGerms_mk (F : Presheaf (Type u) X) (U : Opens X)
    (τ : ∀ x : ↥U, F.stalk x.val) (hpred : (Sheafify.isLocallyGerm F).pred τ) :
    sheafifyGerms F U ⟨τ, hpred⟩ = τ := by
  funext x
  simp only [sheafifyGerms]
  apply (stalkSheafifyEquiv F x.val).injective
  rw [Equiv.apply_symm_apply, stalkSheafifyEquiv_apply]
  have h_bij : Function.Bijective (F.stalkToFiber x.val) := (sheafifyStalkIso F
      x.val).toEquiv.bijective
  apply h_bij.1
  have hrhs : F.stalkToFiber x.val (F.sheafify.presheaf.germ U x.val x.prop ⟨τ, hpred⟩) = τ x :=
    stalkToFiber_germ (Sheafify.isLocallyGerm F) U x.val x.prop ⟨τ, hpred⟩
  rw [stalkToFiber_stalkFunctor_map_toSheafify, hrhs]

/-- A family of germs lying in the fibre product is locally a germ, hence defines a section of the
sheafification. This is the gluing half of the sheaf axiom for `F.sheafify`. -/
private lemma isLocallyGerm_of_piPresheafGerms_eq (F : Presheaf (Type u) X) (U : Opens X)
    (τ : (piPresheaf F).obj (op U)) (h : piPresheafGerms F U τ = piPresheafStalkMap F U τ) :
    (Sheafify.isLocallyGerm F).pred τ := by
  intro x
  obtain ⟨V, hxV, t, W, hxW, hWU, hWV, -, heq_res⟩ :=
    exists_res_eq_of_piPresheafGerms_eq F U τ τ h x
  exact ⟨W, hxW, hWU, ⟨F.map hWV.op t, fun y =>
    (congr_fun heq_res y).trans (germ_res_apply F hWV y.val y.prop t).symm⟩⟩

/-- **Stacks 0084.** The square is a fibre-product diagram of sets: the canonical map
`F^#(U) → Π(F)(U) ×_{∏_x Π(F)_x} ∏_x F_x` is a bijection. -/
@[stacks 0084]
theorem bijective_canonicalToPullback (F : Presheaf (Type u) X) (U : Opens X) :
    Function.Bijective (canonicalToPullback F U) := by
  refine ⟨fun s₁ s₂ h => sheafifyGerms_injective F U (congrArg (fun p => p.val.2) h), ?_⟩
  rintro ⟨⟨τ, σ⟩, hpb⟩
  obtain rfl := pullback_fst_eq_snd F U τ σ hpb
  have hpred := isLocallyGerm_of_piPresheafGerms_eq F U τ hpb
  exact ⟨⟨τ, hpred⟩, Subtype.ext <| Prod.ext (sheafifyGerms_mk F U τ hpred)
    (sheafifyGerms_mk F U τ hpred)⟩

end TopCat.Presheaf
