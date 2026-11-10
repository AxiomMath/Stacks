module

public import StacksFrontier.CategoryTheory.Sites.Modules.Localization.ToposLocalization
public import StacksFrontier.CategoryTheory.Sites.Modules.RingedSite
public import StacksFrontier.CategoryTheory.Sites.Modules.RingedToposHom
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous

/-!
# The direct-sum formula for the lower shriek on modules of a localization

Let `X` be a ringed topos presented by a site `(C, J)`, let `F` be a sheaf of sets on `C` and
let `j : X_F ⟶ X` be the localization `AlgebraicGeometry.RingedTopos.localizedRingedTopos` of
`X` at `F`, on the site of elements of `F`. For a sheaf of modules `G` on `X_F`, Stacks 04IE
part (4) describes the lower shriek `j_!G` as the sheafification of a presheaf of modules whose
sections over an object `V` of `C` are the direct sum, over the sections `s ∈ F(V)`, of the
sections of `G` at the element `(V, s)`:

`(j_!G)^{pre}(V) = ⨁_{s ∈ F(V)} G(V, s)`.

This file builds that presheaf and identifies it with Mathlib's
`PresheafOfModules.pullback` along the structure map of the localization, which is the
presheaf-level lower shriek; `SheafOfModules.pullback` and `SheafOfModules.pullbackIso` supply
the sheafification.

## Main definitions

* `AlgebraicGeometry.RingedTopos.localizedRingSheaf`: the structure sheaf of the localization,
  read as a sheaf of not necessarily commutative rings on the site of elements.
* `AlgebraicGeometry.RingedTopos.elementModuleRingHom`: the structure map of the localization
  on sheaves of (not necessarily commutative) rings. It is the identity, because the structure
  sheaf of the localization *is* the restriction of `O` along the projection.
* `AlgebraicGeometry.RingedTopos.extensionByZeroSummands`: the family of summands, the
  sections of `G` at the elements `(V, s)` for `s ∈ F(V)`.
* `AlgebraicGeometry.RingedTopos.sumPresheaf`: the presheaf of modules `V ↦ ⨁_{s} G(V, s)`.
* `AlgebraicGeometry.RingedTopos.extensionByZeroPresheafSectionIso`: **the direct-sum
  formula**, the canonical identification of the sections of the presheaf-level lower shriek
  with that direct sum.

## Main results

* `AlgebraicGeometry.RingedTopos.extensionByZeroPresheafSectionIso_inv_ι`: the comparison is
  the canonical one — on the summand indexed by `s` it is the component of the unit of the
  presheaf pullback/pushforward adjunction at the element `(V, s)`.
* `AlgebraicGeometry.RingedTopos.moduleRestriction_obj`: Stacks 04IE part (2) on sections — at
  an element `(V, s)` of `F`, the restriction of a sheaf of `O`-modules to the site of elements
  has precisely the sections of the original module over `V`.

## Implementation notes

The identification is `sumPullbackIso`, which exhibits `sumPresheaf` as a left adjoint object
rather than computing the pullback: `sumUnit` is a unit-like map `G ⟶ j_* (⨁ G)`, `sumDesc`
solves the corresponding universal problem, and `sum_hom_ext` says the solution is unique.
`sumPullbackIso` is then the comparison of two solutions of the same universal problem, so no
tensor product is ever unfolded.

Two spellings of the structure map are kept apart. The sheaf-level `elementModuleRingHom` has
the type the source statement gives it, in which the target is spelled with
`CategoryTheory.Functor.sheafPushforwardContinuous`; the presheaf-level
`elementModuleRingPresheafHom` is the very same morphism, named at the result type
`S ⟶ F.op ⋙ R` that `PresheafOfModules.pullback` and `PresheafOfModules.pushforward` ask for.
A projection of a structure-literal definition does not unfold at `implicit` transparency, so
a goal mixing the two spellings is not type-correct there and no `rw` fires in it; naming each
endpoint once and bridging only by definitional unfolding avoids that entirely. For the same
reason `localizedRingSheaf` names the ring sheaf of the localization at the topology
`elementTopology X F`, rather than at `(localizedRingedTopos X F).J`.

`sumFamilyMap` plays the same role one level down: the transition map of `G` between two
elements lands, as written, in a `ModuleCat.restrictScalars` of the summand, and naming it at
the summand itself keeps every subsequent coproduct identity type-correct.

## References

* [Stacks Project, Tag 04IE](https://stacks.math.columbia.edu/tag/04IE)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.RingedTopos

variable (X : RingedTopos.{u, u, u}) (F : X.Topos)

/-- The structure sheaf of the localization of `X` at `F`, read as a sheaf of not necessarily
commutative rings on the site of elements of `F`. -/
noncomputable def localizedRingSheaf : Sheaf (elementTopology X F) RingCat.{u} :=
  (Stacks.SheafOfModules.Tensor.ringSheaf (J := (elementTopology X F))) (localizedRingedTopos X F).O

/-- The structure map of the localization on sheaves of rings, `O_F ⟶ j⁻¹O`. It is the
identity: the structure sheaf of the localization is by definition the restriction of `O`
along the projection from the site of elements. -/
noncomputable def elementModuleRingHom :
    localizedRingSheaf X F ⟶
      ((elementProjection X F).sheafPushforwardContinuous RingCat
        (elementTopology X F) X.J).obj (Stacks.SheafOfModules.Tensor.ringSheaf X.O) :=
  𝟙 _

/-- The structure map of the localization, read on underlying presheaves of rings. This is
`(elementModuleRingHom X F).hom`, named at the result type `S ⟶ F.op ⋙ R` in which Mathlib's
pullback and pushforward of presheaves of modules are indexed. -/
noncomputable def elementModuleRingPresheafHom :
    (localizedRingSheaf X F).obj ⟶
      (elementProjection X F).op ⋙ (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj :=
  (elementModuleRingHom X F).hom

/-- The element `(V, s)` of the site of elements of `F`, for a section `s` of `F` over `V`. -/
abbrev elementObj (V : X.Cᵒᵖ) (s : F.obj.obj V) : (elementSite X F)ᵒᵖ :=
  Opposite.op (CostructuredArrow.mk (yonedaEquiv.symm s))

/-- The morphism of elements `(V, s) ⟶ (W, t)` over a morphism `f : V ⟶ W` of the site along
which `s` restricts to `t`. -/
def elementMap {V W : X.Cᵒᵖ} (f : V ⟶ W)
    (s : F.obj.obj V) (t : F.obj.obj W) (h : F.obj.map f s = t) :
    elementObj X F V s ⟶ elementObj X F W t :=
  (CostructuredArrow.homMk f.unop (by
    apply yonedaEquiv.injective
    simpa [yonedaEquiv] using h)).op

/-- `elementMap` of the identity is the identity. -/
lemma elementMap_id (V : X.Cᵒᵖ) (s : F.obj.obj V) (h : F.obj.map (𝟙 V) s = s) :
    elementMap X F (𝟙 V) s s h = 𝟙 _ :=
  Quiver.Hom.unop_inj (CostructuredArrow.hom_ext _ _ rfl)

/-- `elementMap` of a composite is the composite of the `elementMap`s. -/
lemma elementMap_comp {V W Z : X.Cᵒᵖ} (f : V ⟶ W) (g : W ⟶ Z)
    (s : F.obj.obj V) (t : F.obj.obj W) (r : F.obj.obj Z)
    (h : F.obj.map f s = t) (k : F.obj.map g t = r)
    (l : F.obj.map (f ≫ g) s = r) :
    elementMap X F (f ≫ g) s r l =
      elementMap X F f s t h ≫ elementMap X F g t r k :=
  Quiver.Hom.unop_inj (CostructuredArrow.hom_ext _ _ rfl)

/-- Every object of the site of elements of `F` is an element `(V, s)`. -/
lemma elementObj_induction (P : (elementSite X F)ᵒᵖ → Prop)
    (h : ∀ V s, P (elementObj X F V s)) (A : (elementSite X F)ᵒᵖ) : P A := by
  obtain ⟨V, f, hf⟩ := CostructuredArrow.mk_surjective A.unop
  have hA : A = Opposite.op (CostructuredArrow.mk f) := congrArg Opposite.op hf
  rw [hA, ← yonedaEquiv.symm_apply_apply f]
  exact h (Opposite.op V) (yonedaEquiv f)

/-- Every morphism of elements is the morphism `elementMap` of the morphism of the site
underlying it. -/
lemma elementMap_eq {V W : X.Cᵒᵖ} {s : F.obj.obj V} {t : F.obj.obj W}
    (f : elementObj X F V s ⟶ elementObj X F W t) :
    ∃ h : F.obj.map f.unop.left.op s = t, elementMap X F f.unop.left.op s t h = f := by
  have h : F.obj.map f.unop.left.op s = t := by
    simpa [yonedaEquiv] using congrArg yonedaEquiv f.unop.w
  exact ⟨h, Quiver.Hom.unop_inj (CostructuredArrow.hom_ext _ _ rfl)⟩

/-- The family of summands of the direct-sum formula at the level of presheaves of modules:
the sections of `G` at the elements `(V, s)`, indexed by the sections `s` of `F` over `V`. -/
abbrev sumFamily (G : PresheafOfModules.{u} (localizedRingSheaf X F).obj)
    (V : X.Cᵒᵖ) :
    F.obj.obj V → ModuleCat.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj V) :=
  fun s => G.obj (elementObj X F V s)

/-- The sections of the direct-sum presheaf over `V`: the direct sum `⨁_{s ∈ F(V)} G(V, s)`. -/
noncomputable abbrev sumObj (G : PresheafOfModules.{u} (localizedRingSheaf X F).obj)
    (V : X.Cᵒᵖ) : ModuleCat ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj V) :=
  ∐ sumFamily X F G V

/-- The transition map of `G` from the element `(V, s)` to the element `(W, t)`, named at the
summand `sumFamily X F G W t` in which it lands. -/
noncomputable def sumFamilyMap (G : PresheafOfModules.{u} (localizedRingSheaf X F).obj)
    {V W : X.Cᵒᵖ} (f : V ⟶ W) (s : F.obj.obj V) (t : F.obj.obj W)
    (h : F.obj.map f s = t) (x : sumFamily X F G V s) : sumFamily X F G W t :=
  G.map (elementMap X F f s t h) x

/-- The transition map of `G` along the identity is the identity. -/
lemma sumFamilyMap_id (G : PresheafOfModules.{u} (localizedRingSheaf X F).obj)
    (V : X.Cᵒᵖ) (s : F.obj.obj V) (h : F.obj.map (𝟙 V) s = s)
    (x : sumFamily X F G V s) : sumFamilyMap X F G (𝟙 V) s s h x = x := by
  change G.map (elementMap X F (𝟙 V) s s h) x = _
  rw [elementMap_id, G.map_id]
  rfl

/-- The transition map of `G` along a composite is the composite of the transition maps. -/
lemma sumFamilyMap_comp (G : PresheafOfModules.{u} (localizedRingSheaf X F).obj)
    {V W Z : X.Cᵒᵖ} (f : V ⟶ W) (g : W ⟶ Z)
    (s : F.obj.obj V) (t : F.obj.obj W) (r : F.obj.obj Z)
    (h : F.obj.map f s = t) (k : F.obj.map g t = r) (l : F.obj.map (f ≫ g) s = r)
    (x : sumFamily X F G V s) :
    sumFamilyMap X F G (f ≫ g) s r l x =
      sumFamilyMap X F G g t r k (sumFamilyMap X F G f s t h x) := by
  subst h k
  change G.map (elementMap X F (f ≫ g) s _ l) x = _
  rw [elementMap_comp X F f g s (F.obj.map f s) _ rfl rfl, G.map_comp_apply]
  rfl

/-- The restriction map of the direct-sum presheaf: on the summand indexed by `s` it is the
transition map of `G` to the element `(W, F(f)(s))`, followed by the inclusion of that
summand. -/
noncomputable def sumMap (G : PresheafOfModules.{u} (localizedRingSheaf X F).obj)
    {V W : X.Cᵒᵖ} (f : V ⟶ W) :
    sumObj X F G V ⟶ (ModuleCat.restrictScalars
      ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.map f).hom).obj (sumObj X F G W) :=
  Sigma.desc fun s => G.map (elementMap X F f s (F.obj.map f s) rfl) ≫
    (ModuleCat.restrictScalars ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.map f).hom).map
      (Sigma.ι (sumFamily X F G W) (F.obj.map f s))

/-- The restriction map of the direct-sum presheaf on the summand indexed by `s`: it is the
transition map of `G` to the element `(W, t)`, followed by the inclusion of the summand `t`. -/
lemma sumMap_ι (G : PresheafOfModules.{u} (localizedRingSheaf X F).obj)
    {V W : X.Cᵒᵖ} (f : V ⟶ W)
    (s : F.obj.obj V) (t : F.obj.obj W) (h : F.obj.map f s = t)
    (x : sumFamily X F G V s) :
    sumMap X F G f (Sigma.ι (sumFamily X F G V) s x) =
      Sigma.ι (sumFamily X F G W) t (sumFamilyMap X F G f s t h x) := by
  subst t
  dsimp only [sumMap]
  rw [← ModuleCat.comp_apply, Sigma.ι_comp_desc]
  rfl

/-- **The direct-sum presheaf of modules** `V ↦ ⨁_{s ∈ F(V)} G(V, s)`, whose sheafification is
the lower shriek of `G` along the localization morphism. -/
noncomputable def sumPresheaf (G : PresheafOfModules.{u} (localizedRingSheaf X F).obj) :
    PresheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj where
  obj := sumObj X F G
  map := sumMap X F G
  map_id V := by
    apply Sigma.hom_ext
    intro s
    ext x
    change sumMap X F G (𝟙 V) (Sigma.ι (sumFamily X F G V) s x) = Sigma.ι (sumFamily X F G V) s x
    rw [sumMap_ι X F G (𝟙 V) s s (by simp), sumFamilyMap_id]
  map_comp {V W Z} f g := by
    apply Sigma.hom_ext
    intro s
    ext x
    change sumMap X F G (f ≫ g) (Sigma.ι (sumFamily X F G V) s x) =
      sumMap X F G g (sumMap X F G f (Sigma.ι (sumFamily X F G V) s x))
    rw [sumMap_ι X F G f s (F.obj.map f s) rfl,
      sumMap_ι X F G g (F.obj.map f s) (F.obj.map g (F.obj.map f s)) rfl,
      sumMap_ι X F G (f ≫ g) s (F.obj.map g (F.obj.map f s)) (by simp),
      sumFamilyMap_comp X F G f g s (F.obj.map f s) _ rfl rfl]

/-- The component at an element `A` of the canonical map `G ⟶ j_*(⨁ G)`: the inclusion of the
summand of `A` into the direct sum over the sections of `F` above the object of the site
underlying `A`. -/
noncomputable def sumUnitApp (G : PresheafOfModules.{u} (localizedRingSheaf X F).obj)
    (A : (elementSite X F)ᵒᵖ) :
    G.obj A ⟶ ((PresheafOfModules.pushforward
      (elementModuleRingPresheafHom X F)).obj (sumPresheaf X F G)).obj A := by
  let s := yonedaEquiv A.unop.hom
  let e : G.obj A ≅ G.obj (elementObj X F (Opposite.op A.unop.left) s) :=
    eqToIso (by
      dsimp [elementObj, s]
      rw [Equiv.symm_apply_apply]
      rfl)
  exact e.hom ≫ Sigma.ι (sumFamily X F G (Opposite.op A.unop.left)) s

/-- An `eqToHom` between two summands of a coproduct, followed by the inclusion of one of them,
is the inclusion of the other. -/
lemma coproduct_eqToHom_ι {D : Type*} [Category D]
    {I : Type*} (f : I → D) [HasCoproduct f] {i j : I}
    (h : i = j) (h' : f j = f i) :
    eqToHom h' ≫ Sigma.ι f i = Sigma.ι f j := by
  subst i
  simp

/-- At the element `(V, s)`, the component of `sumUnit` is the inclusion of the summand `s`. -/
lemma sumUnitApp_elementObj (G : PresheafOfModules.{u} (localizedRingSheaf X F).obj)
    (V : X.Cᵒᵖ) (s : F.obj.obj V) :
    sumUnitApp X F G (elementObj X F V s) = Sigma.ι (sumFamily X F G V) s :=
  coproduct_eqToHom_ι (sumFamily X F G V)
    (yonedaEquiv.apply_symm_apply s)
    (congrArg (sumFamily X F G V) (yonedaEquiv.apply_symm_apply s).symm)

/-- The canonical map `G ⟶ j_*(⨁ G)`, the unit of the universal problem solved by the
direct-sum presheaf. -/
noncomputable def sumUnit (G : PresheafOfModules.{u} (localizedRingSheaf X F).obj) :
    G ⟶ (PresheafOfModules.pushforward (elementModuleRingPresheafHom X F)).obj
      (sumPresheaf X F G) where
  app := sumUnitApp X F G
  naturality {A B} f := by
    induction A using elementObj_induction X F
    rename_i V s
    induction B using elementObj_induction X F
    rename_i W t
    obtain ⟨h, hf⟩ := elementMap_eq X F f
    rw [← hf, sumUnitApp_elementObj, sumUnitApp_elementObj]
    ext x
    exact (sumMap_ι X F G _ s t h x).symm

/-- The component of a map `α : G ⟶ j_*N` at the element `(V, s)`, named at the result type
`sumFamily X F G V s ⟶ N.obj V` it has in the category of modules over the sections of `O`
over `V`. -/
noncomputable def sumDescApp (G : PresheafOfModules.{u} (localizedRingSheaf X F).obj)
    (N : PresheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj)
    (α : G ⟶ (PresheafOfModules.pushforward (elementModuleRingPresheafHom X F)).obj N)
    (V : X.Cᵒᵖ) (s : F.obj.obj V) : sumFamily X F G V s ⟶ N.obj V :=
  α.app (elementObj X F V s)

/-- The map out of the direct sum determined by `α`, on the summand indexed by `s`, is the
component of `α` at the element `(V, s)`. -/
lemma sumDesc_ι (G : PresheafOfModules.{u} (localizedRingSheaf X F).obj)
    (N : PresheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj)
    (α : G ⟶ (PresheafOfModules.pushforward (elementModuleRingPresheafHom X F)).obj N)
    (V : X.Cᵒᵖ) (s : F.obj.obj V) (x : sumFamily X F G V s) :
    Sigma.desc (sumDescApp X F G N α V) (Sigma.ι (sumFamily X F G V) s x) =
      sumDescApp X F G N α V s x := by
  rw [← ModuleCat.comp_apply, Sigma.ι_comp_desc]

/-- The map out of the direct-sum presheaf determined by a map `G ⟶ j_*N`: on the summand
indexed by `s` it is the given map at the element `(V, s)`. -/
noncomputable def sumDesc (G : PresheafOfModules.{u} (localizedRingSheaf X F).obj)
    (N : PresheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj)
    (α : G ⟶ (PresheafOfModules.pushforward (elementModuleRingPresheafHom X F)).obj N) :
    sumPresheaf X F G ⟶ N where
  app V := Sigma.desc (sumDescApp X F G N α V)
  naturality {V W} f := by
    apply Sigma.hom_ext
    intro s
    ext x
    change (Sigma.desc (sumDescApp X F G N α W))
        (sumMap X F G f (Sigma.ι (sumFamily X F G V) s x)) =
      N.map f ((Sigma.desc (sumDescApp X F G N α V)) (Sigma.ι (sumFamily X F G V) s x))
    rw [sumMap_ι X F G f s (F.obj.map f s) rfl, sumDesc_ι, sumDesc_ι]
    exact PresheafOfModules.naturality_apply α (elementMap X F f s _ rfl) x

/-- `sumUnit` followed by the pushforward of `sumDesc α` is `α`. -/
lemma sumUnit_desc (G : PresheafOfModules.{u} (localizedRingSheaf X F).obj)
    (N : PresheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj)
    (α : G ⟶ (PresheafOfModules.pushforward (elementModuleRingPresheafHom X F)).obj N) :
    sumUnit X F G ≫ (PresheafOfModules.pushforward
      (elementModuleRingPresheafHom X F)).map (sumDesc X F G N α) = α := by
  apply PresheafOfModules.hom_ext
  intro A
  induction A using elementObj_induction X F
  rename_i V s
  change sumUnitApp X F G (elementObj X F V s) ≫ _ = _
  rw [sumUnitApp_elementObj]
  exact Sigma.ι_comp_desc (sumDescApp X F G N α V) s

/-- Two maps out of the direct-sum presheaf agree once they agree after `sumUnit`. -/
lemma sum_hom_ext (G : PresheafOfModules.{u} (localizedRingSheaf X F).obj)
    (N : PresheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj)
    (a b : sumPresheaf X F G ⟶ N)
    (h : sumUnit X F G ≫
        (PresheafOfModules.pushforward (elementModuleRingPresheafHom X F)).map a =
      sumUnit X F G ≫
        (PresheafOfModules.pushforward (elementModuleRingPresheafHom X F)).map b) : a = b := by
  apply PresheafOfModules.hom_ext
  intro V
  apply Sigma.hom_ext (f := sumFamily X F G V)
  intro s
  have hh := congrArg (fun k => k.app (elementObj X F V s)) h
  change sumUnitApp X F G (elementObj X F V s) ≫ a.app V =
    sumUnitApp X F G (elementObj X F V s) ≫ b.app V at hh
  rwa [sumUnitApp_elementObj] at hh

/-- **The presheaf-level lower shriek is the direct-sum presheaf.** -/
noncomputable def sumPullbackIso (G : PresheafOfModules.{u} (localizedRingSheaf X F).obj) :
    (PresheafOfModules.pullback.{u} (elementModuleRingPresheafHom X F)).obj G ≅
      sumPresheaf X F G := by
  let adj := PresheafOfModules.pullbackPushforwardAdjunction.{u}
    (elementModuleRingPresheafHom X F)
  let a := (adj.homEquiv _ _).symm (sumUnit X F G)
  let b := sumDesc X F G _ (adj.unit.app G)
  have hab : adj.unit.app G ≫
      (PresheafOfModules.pushforward (elementModuleRingPresheafHom X F)).map a =
        sumUnit X F G := (adj.homEquiv _ _).apply_symm_apply _
  have hba := sumUnit_desc X F G _ (adj.unit.app G)
  refine ⟨a, b, ?_, ?_⟩
  · apply (adj.homEquiv _ _).injective
    rw [adj.homEquiv_apply, Functor.map_comp, ← Category.assoc, hab, hba, adj.homEquiv_id]
  · apply sum_hom_ext X F G
    rw [Functor.map_comp, ← Category.assoc, hba, hab]
    exact (Category.comp_id _).symm

/-- The summands of the direct-sum formula: the sections of `G` at the elements `(V, s)` of the
site of elements of `F`, indexed by the sections `s` of `F` over `V`. -/
abbrev extensionByZeroSummands (G : SheafOfModules.{u} (localizedRingSheaf X F)) (V : X.C) :
    F.obj.obj (Opposite.op V) →
      ModuleCat ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj (Opposite.op V)) :=
  sumFamily X F G.val (Opposite.op V)

/-- **Stacks 04IE, part (4): the direct-sum formula.** The sections over `V` of the
presheaf-level lower shriek of `G` along the localization of `X` at `F` are the direct sum,
over the sections `s` of `F` over `V`, of the sections of `G` at the element `(V, s)`. -/
@[stacks 04IE "part (4): direct-sum formula"]
noncomputable def extensionByZeroPresheafSectionIso
    (G : SheafOfModules.{u} (localizedRingSheaf X F)) (V : X.C) :
    ((PresheafOfModules.pullback.{u}
      (F := elementProjection X F)
      (R := (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj)
      (S := (localizedRingSheaf X F).obj)
      (elementModuleRingPresheafHom X F)).obj G.val).obj (Opposite.op V) ≅
      (∐ extensionByZeroSummands X F G V) :=
  (PresheafOfModules.evaluation _ (Opposite.op V)).mapIso (sumPullbackIso X F G.val)

/-- **The direct-sum comparison is the canonical one.** On the summand indexed by a section `s`
of `F` over `V` it is the component, at the element `(V, s)`, of the unit of the adjunction
between the presheaf-level lower shriek and restriction to the site of elements. -/
@[stacks 04IE "part (4): canonical comparison on summands"]
theorem extensionByZeroPresheafSectionIso_inv_ι
    (G : SheafOfModules.{u} (localizedRingSheaf X F)) (V : X.C)
    (s : F.obj.obj (Opposite.op V)) :
    HEq (Limits.Sigma.ι (extensionByZeroSummands X F G V) s ≫
      (extensionByZeroPresheafSectionIso X F G V).inv)
      (((PresheafOfModules.pullbackPushforwardAdjunction.{u}
        (F := elementProjection X F)
        (R := (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj)
        (S := (localizedRingSheaf X F).obj)
        (elementModuleRingPresheafHom X F)).unit.app G.val).app
          (Opposite.op
            (CostructuredArrow.mk (yonedaEquiv.symm s) : elementSite X F))) :=
  heq_of_eq <| Sigma.ι_comp_desc (sumDescApp X F G.val
    ((PresheafOfModules.pullback.{u} (elementModuleRingPresheafHom X F)).obj G.val)
    ((PresheafOfModules.pullbackPushforwardAdjunction.{u}
      (elementModuleRingPresheafHom X F)).unit.app G.val) (Opposite.op V)) s

/-- **Stacks 04IE, part (2): module sections.** At an element `(V, s)` of `F`, the restriction
of a sheaf of `O`-modules to the site of elements has precisely the sections of the original
module over `V`. -/
@[stacks 04IE "part (2): module sections"]
theorem moduleRestriction_obj (G : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
    (V : (elementSite X F)ᵒᵖ) :
    (((SheafOfModules.pushforward (F := elementProjection X F)
      (J := elementTopology X F) (K := X.J)
      (elementModuleRingHom X F)).obj G).val.obj V : Type u) =
      (G.val.obj (Opposite.op ((elementProjection X F).obj V.unop)) : Type u) :=
  rfl

end AlgebraicGeometry.RingedTopos

end
