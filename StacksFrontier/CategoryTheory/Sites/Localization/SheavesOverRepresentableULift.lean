module

public import StacksFrontier.CategoryTheory.Sites.Localization.SheavesOverRepresentable
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Large-valued sheaves on a localized site as sheaves over a representable

Let `C` be a category with morphisms in `Type v` and let `U` be an object of `C`. Stacks 00Y1
identifies sheaves on the localized site `C/U` with sheaves on `C` over the representable `h_U`;
`StacksFrontier.CategoryTheory.Sites.Localization.SheavesOverRepresentable` proves this for sheaves
with values in `Type v`, the universe of the morphisms of `C`. This file proves the same statement
for sheaves with values in any larger universe `Type (max w v)`, the representable then being the
universe-lifted Yoneda presheaf `CategoryTheory.uliftYoneda.{w}.obj U`. That is the form needed for
formal algebraic spaces, which are sheaves of `Type (u + 1)` on a site whose morphisms lie in
`Type u`.

The proof is the source's: a presheaf `G` on `C/U` goes to the coproduct presheaf
`V ↦ ∐_{φ : V ⟶ U} G(V →φ U)` with its evident map to `h_U`, and a presheaf `F` over `h_U` goes to
the presheaf `(X, a) ↦ {s ∈ F(X) | φ(s) = a}` on `C/U`; the two composites are the identity by the
two set-theoretic bijections of the source, and each construction carries sheaves to sheaves.

## Main definitions

* `CategoryTheory.OverShriek.presheafULift`: the coproduct presheaf of a large-valued presheaf on
  `C/U`, and `CategoryTheory.OverShriek.presheafToYonedaULift` its map to `h_U`.
* `CategoryTheory.OverShriek.fiberULift`: the presheaf `(X, a) ↦ {s ∈ F(X) | φ(s) = a}` on `C/U`
  of a large-valued presheaf `F` over `h_U`.
* `CategoryTheory.OverShriek.presheafEquivalenceULift`: **the presheaf level form of Stacks 00Y1**
  for large-valued presheaves, `PSh(C/U) ≌ PSh(C)/h_U`.
* `CategoryTheory.OverShriek.sheafEquivalenceULift`: **Stacks 00Y1** for large-valued sheaves,
  when `h_U` is a sheaf: sheaves on `C/U` are the presheaves on `C` over `h_U` which are sheaves.

## Main results

* `CategoryTheory.OverShriek.isSheaf_fiberULift`: the fibre presheaf is a sheaf.
* `CategoryTheory.OverShriek.isSheaf_presheafULift`: the coproduct presheaf of a sheaf is a sheaf
  when `h_U` is one.
* `CategoryTheory.OverShriek.isSheaf_presheafULift_iff`: and conversely.

## References

* [Stacks Project, Tag 00Y1](https://stacks.math.columbia.edu/tag/00Y1)
* [Stacks Project, Tag 03CD](https://stacks.math.columbia.edu/tag/03CD)
-/

@[expose] public section

open CategoryTheory Opposite

universe w v u

namespace CategoryTheory.OverShriek

variable {C : Type u} [Category.{v} C] {U : C}

/-! ### The coproduct presheaf with large values -/

section Coproduct

variable (G : (Over U)ᵒᵖ ⥤ Type (max w v))

/-- The sections over `V` of the large-valued coproduct presheaf of `G`: pairs of a morphism
`φ : V ⟶ U` and a section of `G` over `V →φ U`. -/
abbrev presheafULiftObj (V : C) : Type (max w v) := Σ φ : V ⟶ U, G.obj (op (Over.mk φ))

/-- Two morphisms `Over.mk ψ ⟶ Over.mk φ` and `Over.mk ψ' ⟶ Over.mk φ` of `C/U` with the same
underlying morphism of `C` restrict a section `s` of `G` over `Over.mk φ` to the same section of
the large-valued coproduct presheaf. -/
lemma presheafULiftObj_mk_eq {V W : C} {φ : W ⟶ U} (s : G.obj (op (Over.mk φ)))
    {ψ ψ' : V ⟶ U} (e : Over.mk ψ ⟶ Over.mk φ) (e' : Over.mk ψ' ⟶ Over.mk φ)
    (h : e.left = e'.left) :
    (⟨ψ, G.map e.op s⟩ : presheafULiftObj.{w} G V) = ⟨ψ', G.map e'.op s⟩ := by
  have h1 := Over.w e
  have h2 := Over.w e'
  simp only [Over.mk_hom, Over.mk_left] at h1 h2
  have hψ : ψ = ψ' := by rw [← h1, ← h2, h]
  subst hψ
  rw [Over.OverMorphism.ext h]

/-- The coproduct presheaf `V ↦ ∐_{φ ∈ Hom_C(V, U)} G(V →φ U)` on `C` of a presheaf `G` on `C/U`
with values in `Type (max w v)`: `(φ, s)` restricts along `g : W ⟶ V` to `(g ≫ φ, s|_{W/U})`. -/
def presheafULift : Cᵒᵖ ⥤ Type (max w v) where
  obj V := presheafULiftObj.{w} G V.unop
  map {X Y} f := ↾fun p =>
    ⟨f.unop ≫ p.1, G.map (Over.homMk f.unop rfl : Over.mk (f.unop ≫ p.1) ⟶ Over.mk p.1).op p.2⟩
  map_id X := by
    ext p : 3
    obtain ⟨φ, s⟩ := p
    refine (presheafULiftObj_mk_eq.{w} G s _ (𝟙 (Over.mk φ)) (by simp)).trans ?_
    simp
  map_comp {X Y Z} f g := by
    ext p : 3
    obtain ⟨φ, s⟩ := p
    refine (presheafULiftObj_mk_eq.{w} G s _
      ((Over.homMk g.unop rfl : Over.mk (g.unop ≫ f.unop ≫ φ) ⟶ Over.mk (f.unop ≫ φ)) ≫
        (Over.homMk f.unop rfl : Over.mk (f.unop ≫ φ) ⟶ Over.mk φ)) (by simp)).trans ?_
    simp only [op_comp, FunctorToTypes.map_comp_apply]
    rfl

/-- Restriction in the coproduct presheaf precomposes the first component. -/
@[simp]
lemma presheafULift_map_apply_fst {X Y : Cᵒᵖ} (f : X ⟶ Y) (p : (presheafULift.{w} G).obj X) :
    ((presheafULift.{w} G).map f p).1 = f.unop ≫ p.1 :=
  rfl

/-- Restriction in the coproduct presheaf of a section built from a section of `G`. -/
lemma presheafULift_map_sigmaMk {A B : Over U} (b : B ⟶ A) (t : G.obj (op A)) :
    (presheafULift.{w} G).map b.left.op (⟨A.hom, t⟩ : (presheafULift.{w} G).obj (op A.left)) =
      ⟨B.hom, G.map b.op t⟩ :=
  presheafULiftObj_mk_eq.{w} G t (Over.homMk b.left rfl : Over.mk (b.left ≫ A.hom) ⟶ Over.mk A.hom)
    b rfl

/-- The structural map `∐_{φ : V ⟶ U} G(V →φ U) ⟶ h_U` of the large-valued coproduct presheaf,
forgetting the section and keeping the morphism to `U`. -/
def presheafToYonedaULift : presheafULift.{w} G ⟶ uliftYoneda.{w}.obj U where
  app _ := ↾fun p => ULift.up p.1
  naturality _ _ _ := rfl

end Coproduct

/-- The large-valued coproduct presheaf as a functor `PSh(C/U) ⥤ PSh(C)`. -/
def presheafFunctorULift : ((Over U)ᵒᵖ ⥤ Type (max w v)) ⥤ (Cᵒᵖ ⥤ Type (max w v)) where
  obj G := presheafULift.{w} G
  map {G G'} η :=
    { app := fun V => ↾fun p => ⟨p.1, η.app (op (Over.mk p.1)) p.2⟩
      naturality := fun {X Y} f => by
        ext p
        obtain ⟨φ, s⟩ := p
        exact congrArg (Sigma.mk (f.unop ≫ φ))
          (NatTrans.naturality_apply η
            (Over.homMk f.unop rfl : Over.mk (f.unop ≫ φ) ⟶ Over.mk φ).op s) }
  map_id _ := by ext V p; exact rfl
  map_comp _ _ := by ext V p; exact rfl

/-- The large-valued coproduct presheaf, viewed as a functor `PSh(C/U) ⥤ PSh(C)/h_U` by means of
its structural map. -/
def presheafFunctorToOverULift :
    ((Over U)ᵒᵖ ⥤ Type (max w v)) ⥤ Over (uliftYoneda.{w}.obj U) :=
  (presheafFunctorULift.{w} (U := U)).toOver (uliftYoneda.{w}.obj U) presheafToYonedaULift.{w}
    (fun {_ _} _ => NatTrans.ext (funext fun _ => rfl))

/-! ### The fibre presheaf with large values -/

section Fiber

variable (T : Over (uliftYoneda.{w}.obj U))

/-- The presheaf on `C/U` of a presheaf `F` on `C` over `h_U`, with structural map `φ`, whose
sections over `(X, a)` are the `s ∈ F(X)` with `φ(s) = a`. -/
def fiberULift : (Over U)ᵒᵖ ⥤ Type (max w v) where
  obj W := {s : T.left.obj (op W.unop.left) // T.hom.app (op W.unop.left) s = ULift.up W.unop.hom}
  map {W W'} g := ↾fun s => ⟨T.left.map g.unop.left.op s.1, by
    rw [NatTrans.naturality_apply T.hom g.unop.left.op s.1, s.2]
    exact congrArg ULift.up (Over.w g.unop)⟩
  map_id _ := by ext s; simp
  map_comp f g := by
    ext s
    simp only [unop_comp, Over.comp_left, op_comp, T.left.map_comp_apply]
    rfl

/-- The inclusion of the fibre presheaf into the restriction of `F` to `C/U`. -/
def fiberULiftι : fiberULift.{w} T ⟶ (Over.forget U).op ⋙ T.left where
  app := fun _ => ↾fun s => s.1
  naturality _ _ _ := rfl

end Fiber

/-- A morphism of presheaves over `h_U` induces a map of fibre presheaves. -/
def fiberULiftMap {T T' : Over (uliftYoneda.{w}.obj U)} (f : T ⟶ T') :
    fiberULift.{w} T ⟶ fiberULift.{w} T' where
  app W := ↾fun s => ⟨f.left.app (op W.unop.left) s.1, by
    rw [← NatTrans.comp_app_apply, Over.w f, s.2]⟩
  naturality {W W'} g := by
    ext s
    refine Subtype.ext ?_
    exact NatTrans.naturality_apply f.left g.unop.left.op s.1

/-- The fibre construction as a functor `PSh(C)/h_U ⥤ PSh(C/U)`. -/
@[sga "3 I 1.4"]
def fiberFunctorULift : Over (uliftYoneda.{w}.obj U) ⥤ ((Over U)ᵒᵖ ⥤ Type (max w v)) where
  obj T := fiberULift.{w} T
  map f := fiberULiftMap.{w} f
  map_id _ := by ext W s; rfl
  map_comp f g := by ext W s; rfl

/-! ### The presheaf level equivalence -/

/-- The sections of `G` over `(X, a)` are the sections `(ψ, s)` of the coproduct presheaf over `X`
with `ψ = a`. -/
def presheafUnitEquivULift (G : (Over U)ᵒᵖ ⥤ Type (max w v)) (W : (Over U)ᵒᵖ) :
    G.obj W ≃ (fiberULift.{w} (presheafFunctorToOverULift.{w}.obj G)).obj W :=
  ((Equiv.subtypeEquivRight (fun _ => ULift.up_inj)).trans
    (Equiv.sigmaSubtype (β := fun ψ : W.unop.left ⟶ U => G.obj (op (Over.mk ψ)))
      W.unop.hom)).symm

/-- A presheaf `F` over `h_U` is the disjoint union of the fibres of its structural map. -/
def presheafCounitEquivULift (T : Over (uliftYoneda.{w}.obj U)) (V : Cᵒᵖ) :
    (presheafULift.{w} (fiberULift.{w} T)).obj V ≃ T.left.obj V where
  toFun p := p.2.1
  invFun x := ⟨(T.hom.app V x).down, ⟨x, rfl⟩⟩
  left_inv p := Sigma.subtype_ext (β := T.left.obj V)
    (p := fun φ x => T.hom.app V x = ULift.up φ) (congrArg ULift.down p.2.2) rfl
  right_inv _ := rfl

/-- The unit isomorphism of `CategoryTheory.OverShriek.presheafEquivalenceULift`. -/
def presheafUnitIsoULift :
    𝟭 ((Over U)ᵒᵖ ⥤ Type (max w v)) ≅
      presheafFunctorToOverULift.{w} ⋙ fiberFunctorULift.{w} :=
  NatIso.ofComponents
    (fun G => NatIso.ofComponents (fun W => (presheafUnitEquivULift.{w} G W).toIso)
      (fun {W W'} g => by
        ext s
        exact Subtype.ext (presheafULiftObj_mk_eq.{w} G s
          (Over.homMk g.unop.left rfl : Over.mk (g.unop.left ≫ W.unop.hom) ⟶ Over.mk W.unop.hom)
          g.unop rfl).symm))
    (fun _ => by ext W s; refine Subtype.ext ?_; rfl)

/-- The counit isomorphism of `CategoryTheory.OverShriek.presheafEquivalenceULift`. -/
def presheafCounitIsoULift :
    fiberFunctorULift.{w} ⋙ presheafFunctorToOverULift.{w} ≅ 𝟭 (Over (uliftYoneda.{w}.obj U)) :=
  NatIso.ofComponents
    (fun T => Over.isoMk (NatIso.ofComponents (fun V => (presheafCounitEquivULift.{w} T V).toIso)
        (fun _ => by ext p; rfl)) (by ext V p; exact p.2.property))
    (fun _ => by ext V p; rfl)

/-- **The presheaf level form of Stacks 00Y1, for large-valued presheaves.** Presheaves on `C/U`
with values in `Type (max w v)` are the same thing as such presheaves on `C` over the
universe-lifted representable `h_U`, through the coproduct presheaf and the fibre presheaf. -/
def presheafEquivalenceULift :
    ((Over U)ᵒᵖ ⥤ Type (max w v)) ≌ Over (uliftYoneda.{w}.obj U) where
  functor := presheafFunctorToOverULift.{w}
  inverse := fiberFunctorULift.{w}
  unitIso := presheafUnitIsoULift.{w}
  counitIso := presheafCounitIsoULift.{w}
  functor_unitIso_comp _ := by ext V p; rfl

/-- The functor of `CategoryTheory.OverShriek.presheafEquivalenceULift`, followed by forgetting
the map to `h_U`, is the large-valued coproduct presheaf. -/
lemma presheafEquivalenceULift_functor_comp_forget :
    (presheafEquivalenceULift.{w} (U := U)).functor ⋙ Over.forget (uliftYoneda.{w}.obj U) =
      presheafFunctorULift.{w} :=
  rfl

/-! ### Sheaves -/

section Sheaves

/-- **The fibre presheaf is a sheaf.** If the restriction of `F` to `C/U` is a sheaf and the
restriction of `h_U` is separated, then the fibre presheaf of `F ⟶ h_U` is a sheaf on `C/U`. -/
lemma isSheaf_fiberULift {K : GrothendieckTopology (Over U)} (T : Over (uliftYoneda.{w}.obj U))
    (hF : Presieve.IsSheaf K ((Over.forget U).op ⋙ T.left))
    (hA : Presieve.IsSeparated K ((Over.forget U).op ⋙ uliftYoneda.{w}.obj U)) :
    Presieve.IsSheaf K (fiberULift.{w} T) := by
  intro W S hS x hx
  obtain ⟨t, ht, htu⟩ := hF S hS (x.map (fiberULiftι.{w} T)) (hx.map _)
  have hmem : T.hom.app (op W.left) t = ULift.up W.hom := by
    refine (hA S hS).ext (fun {Y} {f} hf => ?_)
    simp only [Functor.comp_map, Functor.op_map, Over.forget_map, Quiver.Hom.unop_op]
    rw [← NatTrans.naturality_apply T.hom f.left.op t,
      show T.left.map f.left.op t = (x f hf).1 from ht f hf, (x f hf).2]
    exact congrArg ULift.up (Over.w f).symm
  exact ⟨⟨t, hmem⟩, fun {Y} f hf => Subtype.ext (ht f hf),
    fun y hy => Subtype.ext (htu y.1 fun {Y} f hf => congrArg Subtype.val (hy f hf))⟩

variable {G : (Over U)ᵒᵖ ⥤ Type (max w v)}

/-- The section of `G` over `A` carried by a section `p` of the coproduct presheaf over `A.left`
whose first component is the structure morphism of `A`. -/
def presheafULiftSection {A : Over U} (p : (presheafULift.{w} G).obj (op A.left))
    (h : p.1 = A.hom) :
    G.obj (op A) :=
  G.map (Over.homMk (𝟙 A.left) (by simpa using h) : A ⟶ Over.mk p.1).op p.2

/-- The first component of a section of the coproduct presheaf is preserved by restriction. -/
lemma presheafULiftSection_fst {A B : Over U} (b : B ⟶ A)
    {p : (presheafULift.{w} G).obj (op A.left)}
    (h : p.1 = A.hom) {q : (presheafULift.{w} G).obj (op B.left)}
    (hq : (presheafULift.{w} G).map b.left.op p = q) : q.1 = B.hom := by
  subst hq
  rw [presheafULift_map_apply_fst, Quiver.Hom.unop_op, h]
  exact Over.w b

/-- Rebuilding a section of the coproduct presheaf from the section of `G` it carries recovers
it. -/
lemma sigmaMk_presheafULiftSection {A : Over U} (p : (presheafULift.{w} G).obj (op A.left))
    (h : p.1 = A.hom) :
    (⟨A.hom, presheafULiftSection.{w} p h⟩ : (presheafULift.{w} G).obj (op A.left)) = p := by
  refine (presheafULiftObj_mk_eq.{w} G p.2
    (Over.homMk (𝟙 A.left) (by simpa using h) : Over.mk A.hom ⟶ Over.mk p.1)
    (𝟙 (Over.mk p.1)) (by simp)).trans ?_
  simp only [op_id, FunctorToTypes.map_id_apply]
  rfl

/-- The section of `G` carried by a section of the coproduct presheaf is compatible with
restriction. -/
lemma map_presheafULiftSection {A B : Over U} (b : B ⟶ A)
    {p : (presheafULift.{w} G).obj (op A.left)}
    (h : p.1 = A.hom) {q : (presheafULift.{w} G).obj (op B.left)}
    (hq : (presheafULift.{w} G).map b.left.op p = q) :
    G.map b.op (presheafULiftSection.{w} p h) =
      presheafULiftSection.{w} q (presheafULiftSection_fst.{w} b h hq) :=
  eq_of_heq (Sigma.mk.inj <|
    (presheafULift_map_sigmaMk.{w} G b (presheafULiftSection.{w} p h)).symm.trans <|
      ((congrArg (fun z => (presheafULift.{w} G).map b.left.op z)
        (sigmaMk_presheafULiftSection.{w} p h)).trans hq).trans
        (sigmaMk_presheafULiftSection.{w} q (presheafULiftSection_fst.{w} b h hq)).symm).2

/-- The large-valued coproduct presheaf of a sheaf on `C/U` is a sheaf on `C`, provided the
universe-lifted representable presheaf of `U` is one. -/
lemma isSheaf_presheafULift (J : GrothendieckTopology C)
    (hU : Presieve.IsSheaf J (uliftYoneda.{w}.obj U)) (hG : Presieve.IsSheaf (J.over U) G) :
    Presieve.IsSheaf J (presheafULift.{w} G) := by
  intro V S hS x hx
  obtain ⟨φ, hφ, hφuniq⟩ := hU S hS _ (hx.map (presheafToYonedaULift.{w} G))
  have key : ∀ {A : Over U} (a : A ⟶ Over.mk φ.down) (ha : S.arrows a.left),
      (x a.left ha).1 = A.hom := fun a ha =>
    (congrArg ULift.down (hφ a.left ha)).symm.trans (Over.w a)
  obtain ⟨t, ht, htuniq⟩ :=
    hG _ (J.overEquiv_symm_mem_over (Over.mk φ.down) S hS)
      (fun _ a ha => presheafULiftSection.{w} (x a.left ha) (key a ha))
      (by
        intro _ _ _ b₁ b₂ _ _ h₁ h₂ hcomm
        exact (map_presheafULiftSection.{w} b₁ _ rfl).trans
          (map_presheafULiftSection.{w} b₂ _
            (hx b₁.left b₂.left h₁ h₂ (congrArg Over.Hom.left hcomm)).symm).symm)
  refine ⟨⟨φ.down, t⟩, fun Y f hf => ?_, fun p hp => ?_⟩
  · let b : Over.mk (f ≫ φ.down) ⟶ Over.mk φ.down := Over.homMk f rfl
    exact (presheafULift_map_sigmaMk.{w} G b t).trans
      ((congrArg (fun s => (⟨f ≫ φ.down, s⟩ : (presheafULift.{w} G).obj (op Y))) (ht b hf)).trans
        (sigmaMk_presheafULiftSection.{w} (A := Over.mk (f ≫ φ.down)) (x f hf) (key b hf)))
  · have hψ : p.1 = φ.down :=
      congrArg ULift.down (hφuniq _ (hp.map (presheafToYonedaULift.{w} G)))
    exact (sigmaMk_presheafULiftSection.{w} (A := Over.mk φ.down) p hψ).symm.trans
      (congrArg (fun s => (⟨φ.down, s⟩ : (presheafULift.{w} G).obj (op V)))
        (htuniq _ fun _ a ha => map_presheafULiftSection.{w} a hψ (hp a.left ha)))

/-- The large-valued coproduct presheaf of a presheaf `G` on `C/U` is a sheaf on `C` if and only
if `G` is a sheaf on `C/U`, provided the universe-lifted representable presheaf of `U` is a
sheaf. -/
lemma isSheaf_presheafULift_iff (J : GrothendieckTopology C)
    (hU : Presieve.IsSheaf J (uliftYoneda.{w}.obj U)) :
    Presieve.IsSheaf J (presheafULift.{w} G) ↔ Presieve.IsSheaf (J.over U) G := by
  refine ⟨fun h => ?_, isSheaf_presheafULift.{w} J hU⟩
  have restrict : ∀ P : Cᵒᵖ ⥤ Type (max w v), Presieve.IsSheaf J P →
      Presieve.IsSheaf (J.over U) ((Over.forget U).op ⋙ P) := fun P hP =>
    (isSheaf_iff_isSheaf_of_type _ _).1
      (Sheaf.over (⟨_, (isSheaf_iff_isSheaf_of_type _ _).2 hP⟩ :
        Sheaf J (Type (max w v))) U).property
  exact (Presieve.isSheaf_iso (J.over U) (presheafUnitIsoULift.{w}.app G).symm)
    (isSheaf_fiberULift.{w} _ (restrict _ h) (restrict _ hU).isSeparated)

/-- The presheaves on `C` over `h_U` whose underlying presheaf is a sheaf. -/
abbrev IsSheafLeft (J : GrothendieckTopology C) : ObjectProperty (Over (uliftYoneda.{w}.obj U)) :=
  fun T => Presheaf.IsSheaf J T.left

/-- Being a sheaf on the underlying presheaf is invariant under isomorphism in the over category
of `h_U`. -/
instance (J : GrothendieckTopology C) :
    (IsSheafLeft.{w} (U := U) J).IsClosedUnderIsomorphisms where
  of_iso e h := (Presheaf.isSheaf_of_iso_iff ((Over.forget _).mapIso e)).1 h

/-- **Stacks 00Y1, for large-valued sheaves.** When the universe-lifted representable presheaf of
`U` is a sheaf, sheaves on the localized site `C/U` with values in `Type (max w v)` are the same
thing as presheaves on `C` over `h_U` which are sheaves. This is
`CategoryTheory.OverShriek.presheafEquivalenceULift` restricted to sheaves on both sides. -/
def sheafEquivalenceULift (J : GrothendieckTopology C)
    (hU : Presieve.IsSheaf J (uliftYoneda.{w}.obj U)) :
    Sheaf (J.over U) (Type (max w v)) ≌ (IsSheafLeft.{w} (U := U) J).FullSubcategory :=
  presheafEquivalenceULift.{w}.congrFullSubcategory (by
    ext G
    change Presheaf.IsSheaf J (presheafULift.{w} G) ↔ Presheaf.IsSheaf (J.over U) G
    rw [isSheaf_iff_isSheaf_of_type, isSheaf_iff_isSheaf_of_type]
    exact isSheaf_presheafULift_iff J hU)

end Sheaves

end CategoryTheory.OverShriek

end
