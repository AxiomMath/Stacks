module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.Perfect.InvertibleObjectsClauseOneToTwo
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Perfect.LeftDualLocalRetractOnASite
public import StacksFrontier.CategoryTheory.Sites.Cohomology.TensorComplex.RestrictionSections

/-!
# An invertible object is, over the members of a covering, a retract of a subcomplex

Let `(C, O)` be a ringed site, let `ℳ` and `𝒩` be K-flat complexes of `O`-modules and let
`γ : Tot(ℳ ⊗ 𝒩) ≅ O[0]` be an isomorphism of `D(O)`, so that `Q(ℳ)` is an invertible object of
`D(O)` with inverse `Q(𝒩)`. Suppose that over an object `W` of `C` the inverse of `γ` is the class
of the map of complexes `O|_W[0] ⟶ Tot(ℳ ⊗ 𝒩)|_W` attached to a degree-zero cocycle section `t`
of `Tot(ℳ ⊗ 𝒩)` over `W`. Then for every complex `𝒦` on the localized site `C/W` and every map
`ι : 𝒦 ⟶ ℳ|_W` whose tensor product with `𝒩|_W` is a monomorphism in degree one, and through
which the restriction of `t` lifts, `ℳ|_W` is a retract of `𝒦` in `D(O|_W)`.

This is the direct-summand step of the source's proof of the first assertion of Stacks 0FPV,
"we conclude that `M` is a direct summand of `K` in `D(O)`", for an invertible `M`, with the
subcomplex `𝒦` living on the localized site, where the finitely many sections `fᵢ` it has to
contain are sections over the final object.

## Main results

* `CategoryTheory.nonempty_retract_of_tensorIsoUnit_inv_eq`: in a monoidal category, if
  `e : A ⊗ B ≅ 𝟙` and `e⁻¹` factors through `j ▷ B` for some `j : K ⟶ A`, and `B ⊗ A ⟶ 𝟙` is
  some isomorphism, then `A` is a retract of `K`.
* `AlgebraicGeometry.RingedSite.InvertibleDerived.nonempty_retract_restrictMod_of_tensorIsoUnit`:
  the statement above.
* `AlgebraicGeometry.RingedSite.InvertibleDerived.whiskerRight_f_sum_eq_tensorComplexOverIso`:
  the pure-tensor input of that statement.

## Implementation notes

**Why invertible, and why the localized site.** For a general left dual the retraction is the
triangle identity, and on the localized site it needs the coevaluation of the *restricted*
pairing, which is read through the tensorator of derived restriction; that tensorator is built by
localization and its value on local pure tensors is not accessible. For an invertible object no
triangle identity is needed: the composite
`A ⟶ 𝟙 ⊗ A ⟶ (A ⊗ B) ⊗ A ⟶ A ⊗ (B ⊗ A) ⟶ A ⊗ 𝟙 ⟶ A` of isomorphisms is an isomorphism whatever
the isomorphisms are, and it factors through `K` as soon as `e⁻¹` does. So on `C/W` the
isomorphism `e` is assembled directly from `γ` and the chain-level restriction comparison
`AlgebraicGeometry.RingedSite.tensorComplexOverIso`, whose value on local pure tensors is known
(`AlgebraicGeometry.RingedSite.tensorComplexOverIso_inv_tensorComplexSection`), and no monoidal
structure on restriction enters.

The subcomplex `𝒦` must live on `C/W` and not on `C`: a subcomplex of `ℳ` on `C` containing a
section over `W` contains its image under every arrow `V ⟶ W`, and its restriction to `C/W` is
then of finite type only for a subterminal `W`.

## References

* [Stacks Project, Tag 0FPV](https://stacks.math.columbia.edu/tag/0FPV)
* [Stacks Project, Tag 0FPY](https://stacks.math.columbia.edu/tag/0FPY)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry
open Opposite Stacks.SheafOfModules.DerivedMonoidal

universe u v w

namespace CategoryTheory

/-- **A retract from a factorization of the inverse of a tensor isomorphism.** Let
`e : A ⊗ B ≅ 𝟙` and let `g : B ⊗ A ⟶ 𝟙` be an isomorphism. If `e⁻¹` factors as
`c ≫ (j ▷ B)` for some `j : K ⟶ A`, then `A` is a retract of `K`, with `j` followed by an
automorphism of `A` as the retraction. -/
theorem nonempty_retract_of_tensorIsoUnit_inv_eq {C : Type u} [Category.{v} C]
    [MonoidalCategory C] {A B K : C} (e : A ⊗ B ≅ 𝟙_ C) (g : B ⊗ A ⟶ 𝟙_ C) [IsIso g]
    (j : K ⟶ A) (c : 𝟙_ C ⟶ K ⊗ B) (hc : c ≫ (j ▷ B) = e.inv) :
    Nonempty (Retract A K) := by
  let θ : A ⟶ A := (λ_ A).inv ≫ (e.inv ▷ A) ≫ (α_ A B A).hom ≫ (A ◁ g) ≫ (ρ_ A).hom
  let s : A ⟶ K := (λ_ A).inv ≫ (c ▷ A) ≫ (α_ K B A).hom ≫ (K ◁ g) ≫ (ρ_ K).hom
  have hθ : s ≫ j = θ := by
    simp only [s, θ, Category.assoc, ← hc, comp_whiskerRight]
    rw [← rightUnitor_naturality, whisker_exchange_assoc, ← associator_naturality_left_assoc]
  have : IsIso θ := by
    dsimp only [θ]
    infer_instance
  exact ⟨⟨s, j ≫ inv θ, by rw [← Category.assoc, hθ, IsIso.hom_inv_id]⟩⟩

end CategoryTheory

namespace AlgebraicGeometry.RingedSite.InvertibleDerived

attribute [local instance] SheafOfModules.monoidalCategorySheafTensor
  SheafOfModules.symmetricCategorySheafTensor SheafOfModules.monoidalPreadditiveSheafTensor
  SheafOfModules.monoidalClosedSheafTensor
  SheafOfModules.preservesColimit_tensorRight_sheafTensor
  CochainComplex.symmetricCategory

attribute [local instance 10000] HasDerivedCategory.standard

attribute [local instance] ringSheafSectionsCommRing ringSheafOverSectionsCommRing

attribute [local implicit_reducible]
  Stacks.SheafOfModules.Tensor.tensorComplex
  CategoryTheory.sheafCompose
  CategoryTheory.Functor.sheafPushforwardContinuous
  ModuleCat.restrictScalars
  ModuleCat.RestrictScalars.obj'
  PresheafOfModules.pushforward
  PresheafOfModules.pushforward₀
  PresheafOfModules.pushforward₀Obj
  PresheafOfModules.presheaf
  PresheafOfModules.toPresheaf
  PresheafOfModules.restrictScalars
  PresheafOfModules.restrictScalarsObj
  SheafOfModules.pushforward
  SheafOfModules.overFunctor
  SheafOfModules.toSheaf
  SheafOfModules.forget

variable {X : RingedSite.{u, u, u}} [HasSheafify X.J AddCommGrpCat.{u}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [∀ W : X.C, HasSheafify (X.J.over W) AddCommGrpCat.{u}]
  [∀ W : X.C, (X.J.over W).WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- The morphism out of the structure sheaf of the localized site `C/W` sending `1` to a
prescribed section over the final object `W`. -/
def unitHomOfTerminal {W : X.C} (F : Mod (X.over W).O)
    (s : F.val.obj (op (Over.mk (𝟙 W)))) :
    SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf (X.over W).O) ⟶ F :=
  (SheafOfModules.unitHomEquiv F).symm
    (PresheafOfModules.sectionsMk
      (fun V => F.val.map (Over.homMk V.unop.hom : V.unop ⟶ Over.mk (𝟙 W)).op s)
      (fun V V' f => by
        rw [← PresheafOfModules.map_comp_apply]
        exact F.val.congr_map_apply
          (Quiver.Hom.unop_inj (Over.OverMorphism.ext (by
            simp only
            exact Over.w f.unop))) s))

omit [HasSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [∀ W : X.C, HasSheafify (X.J.over W) AddCommGrpCat.{u}]
  [∀ W : X.C, (X.J.over W).WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- `unitHomOfTerminal` sends `1` to the section it was built from. -/
theorem unitHomOfTerminal_val_app {W : X.C} (F : Mod (X.over W).O)
    (s : F.val.obj (op (Over.mk (𝟙 W)))) :
    (unitHomOfTerminal F s).val.app (op (Over.mk (𝟙 W)))
      (1 : ((Stacks.SheafOfModules.Tensor.ringSheaf (X.over W).O).obj.obj
        (op (Over.mk (𝟙 W))))) = s := by
  refine (SheafOfModules.unitHomEquiv_symm_val_app_one F _ _).trans ?_
  change F.val.map _ s = s
  have hid : (Over.homMk (Over.mk (𝟙 W)).hom : Over.mk (𝟙 W) ⟶ Over.mk (𝟙 W)).op = 𝟙 _ :=
    Quiver.Hom.unop_inj (Over.OverMorphism.ext (by simp))
  rw [hid, PresheafOfModules.map_id]
  rfl

omit [HasSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [∀ W : X.C, HasSheafify (X.J.over W) AddCommGrpCat.{u}]
  [∀ W : X.C, (X.J.over W).WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- **A morphism out of the structure sheaf of the localized site `C/W` is determined by the image
of `1` over the final object `W`.** -/
theorem unitHom_ext_of_terminal {W : X.C} {F : Mod (X.over W).O}
    {f g : SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf (X.over W).O) ⟶ F}
    (h : f.val.app (op (Over.mk (𝟙 W)))
        (1 : ((Stacks.SheafOfModules.Tensor.ringSheaf (X.over W).O).obj.obj
          (op (Over.mk (𝟙 W))))) =
      g.val.app (op (Over.mk (𝟙 W)))
        (1 : ((Stacks.SheafOfModules.Tensor.ringSheaf (X.over W).O).obj.obj
          (op (Over.mk (𝟙 W)))))) :
    f = g := by
  refine (SheafOfModules.unitHomEquiv F).injective (Subtype.ext (funext fun V => ?_))
  obtain ⟨V⟩ := V
  let k : V ⟶ Over.mk (𝟙 W) := Over.homMk V.hom
  rw [← (SheafOfModules.unitHomEquiv F f).2 k.op, ← (SheafOfModules.unitHomEquiv F g).2 k.op,
    SheafOfModules.unitHomEquiv_apply_coe, SheafOfModules.unitHomEquiv_apply_coe]
  exact congrArg (F.val.map k.op) h

/-- An isomorphism of complexes of sheaves of modules undoes its inverse on local sections. -/
theorem iso_hom_f_val_app_inv_f {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    {R : Sheaf J RingCat.{w}} {K L : CochainComplex (SheafOfModules.{w} R) ℤ} (e : K ≅ L)
    (n : ℤ) (V : Cᵒᵖ) (z : (L.X n).val.obj V) :
    (e.hom.f n).val.app V ((e.inv.f n).val.app V z) = z := by
  change ((e.inv ≫ e.hom).f n).val.app V z = z
  rw [e.inv_hom_id]
  rfl

/-- The section of the restricted total tensor complex over the final object of `C/W` attached
to a section over `W` is the one the comparison `tensorComplexOverIso` produces from finitely many
pure tensors, read in the other direction. -/
theorem tensorComplexOverIso_hom_sum {W : X.C} (Mc Nc : CochainComplex (Mod X.O) ℤ)
    {κ : Type} [Fintype κ] (deg rdeg : κ → ℤ) (hdeg : ∀ i, deg i + rdeg i = 0)
    (a : ∀ i, (Mc.X (deg i)).val.obj (op W)) (b : ∀ i, (Nc.X (rdeg i)).val.obj (op W)) :
    ((tensorComplexOverIso X W Mc Nc).hom.f 0).val.app (op (Over.mk (𝟙 W)))
        (∑ i, tensorComplexSection X (deg i) (rdeg i) 0 (hdeg i) (a i) (b i)) =
      ∑ i, tensorComplexSection (X.over W) (deg i) (rdeg i) 0 (hdeg i)
        (K := restrictMod Mc W) (L := restrictMod Nc W) (W := Over.mk (𝟙 W)) (a i) (b i) := by
  refine Eq.trans (congrArg (((tensorComplexOverIso X W Mc Nc).hom.f 0).val.app
    (op (Over.mk (𝟙 W)))) ?_) (iso_hom_f_val_app_inv_f (tensorComplexOverIso X W Mc Nc) 0 _ _)
  refine Eq.symm ((map_sum (((tensorComplexOverIso X W Mc Nc).inv.f 0).val.app
    (op (Over.mk (𝟙 W)))).hom _ Finset.univ).trans ?_)
  exact Finset.sum_congr rfl fun i _ =>
    tensorComplexOverIso_inv_tensorComplexSection X W Mc Nc (Over.mk (𝟙 W)) (deg i)
      (rdeg i) 0 (hdeg i) (a i) (b i)

/-- Restriction to the localized site preserves finite limits. -/
instance ovFPreservesFiniteLimits (W : X.C) : PreservesFiniteLimits (ovF X W) :=
  Stacks.SheafOfModules.LocalCokernel.overFunctor_preservesFiniteLimits
    (R := Stacks.SheafOfModules.Tensor.ringSheaf X.O) W

/-- Restriction to the localized site preserves finite colimits. -/
instance ovFPreservesFiniteColimits (W : X.C) : PreservesFiniteColimits (ovF X W) :=
  Stacks.SheafOfModules.LocalCokernel.overFunctor_preservesFiniteColimits
    (R := Stacks.SheafOfModules.Tensor.ringSheaf X.O) W

/-! ### The data on the localized site, at one spelling

The structure sheaf of the localized site `C/W` has three spellings which are definitionally
equal and not reducibly so: `(Stacks.SheafOfModules.Tensor.ringSheaf X.O).over W`, in which
`SheafOfModules.cocycleHomOver` is stated, `Stacks.SheafOfModules.Tensor.ringSheaf (X.O.over W)`,
in which `AlgebraicGeometry.RingedSite.tensorComplexOverIso` is stated, and
`Stacks.SheafOfModules.Tensor.ringSheaf (X.over W).O`, in which the derived tensor product of
`C/W` is stated. Each datum below is the corresponding datum of the ambient development with its
type written at the third spelling, so that the definitional unfolding happens once, here, and
every later statement is at a single spelling. -/

/-- The structure sheaf of the localized site in degree zero. -/
abbrev sliceUnitComplex (W : X.C) : Complexes (X.over W).O :=
  (CochainComplex.singleFunctor (Mod (X.over W).O) 0).obj
    (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf (X.over W).O))

/-- The restriction of `O[0]` to the localized site is its structure sheaf in degree zero. -/
def sliceUnitComplexIso (W : X.C) :
    (restrictMod X.structureSheafComplex W : Complexes (X.over W).O) ≅ sliceUnitComplex W :=
  SheafOfModules.overFunctorUnitComplexIso (Stacks.SheafOfModules.Tensor.ringSheaf X.O) W

/-- The map of complexes out of the structure sheaf of the localized site attached to a
degree-zero cocycle section over `W` of a complex on `C`. -/
def sliceCocycleHom (W : X.C) (A : Complexes X.O) (t : (A.X 0).val.obj (op W))
    (ht : (A.d 0 1).val.app (op W) t = 0) :
    sliceUnitComplex W ⟶ (restrictMod A W : Complexes (X.over W).O) :=
  SheafOfModules.cocycleHomOver (Stacks.SheafOfModules.Tensor.ringSheaf X.O) A W t ht

/-- The restriction of a total tensor complex is the total tensor complex of the
restrictions. -/
def sliceTensorIso (W : X.C) (Mc Nc : Complexes X.O) :
    (restrictMod (Mc ⊗ Nc : Complexes X.O) W : Complexes (X.over W).O) ≅
      (restrictMod Mc W ⊗ restrictMod Nc W : Complexes (X.over W).O) :=
  tensorComplexOverIso X W Mc Nc

/-- **The degree-zero section over the final object which a map of complexes out of the structure
sheaf of the localized site sends `1` to.** -/
def sliceCocycleOf {W : X.C} {L : Complexes (X.over W).O} (φ : sliceUnitComplex W ⟶ L) :
    (L.X 0).val.obj (op (Over.mk (𝟙 W))) :=
  ((HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
    (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf (X.over W).O))).inv ≫
      φ.f 0).val.app (op (Over.mk (𝟙 W)))
    (1 : ((Stacks.SheafOfModules.Tensor.ringSheaf (X.over W).O).obj.obj (op (Over.mk (𝟙 W)))))

omit [HasSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [∀ W : X.C, HasSheafify (X.J.over W) AddCommGrpCat.{u}]
  [∀ W : X.C, (X.J.over W).WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- `sliceCocycleOf` is natural in the target. -/
theorem sliceCocycleOf_comp {W : X.C} {L L' : Complexes (X.over W).O}
    (φ : sliceUnitComplex W ⟶ L) (g : L ⟶ L') :
    sliceCocycleOf (φ ≫ g) = (g.f 0).val.app (op (Over.mk (𝟙 W))) (sliceCocycleOf φ) :=
  rfl

omit [HasSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [∀ W : X.C, HasSheafify (X.J.over W) AddCommGrpCat.{u}]
  [∀ W : X.C, (X.J.over W).WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- The section a map of complexes out of the structure sheaf of the localized site produces is a
cocycle. -/
theorem sliceCocycleOf_d {W : X.C} {L : Complexes (X.over W).O} (φ : sliceUnitComplex W ⟶ L) :
    (L.d 0 1).val.app (op (Over.mk (𝟙 W))) (sliceCocycleOf φ) = 0 := by
  have hd : (sliceUnitComplex W).d 0 1 = 0 :=
    HomologicalComplex.single_obj_d (V := Mod (X.over W).O) (c := ComplexShape.up ℤ) 0
      (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf (X.over W).O)) 0 1
  have h1 : φ.f 0 ≫ L.d 0 1 = 0 := (φ.comm 0 1).trans (by rw [hd, zero_comp])
  have h2 : (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
      (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf (X.over W).O))).inv ≫
        φ.f 0 ≫ L.d 0 1 = 0 := by
    rw [h1, comp_zero]
  exact (congrArg (fun ψ => ψ.val.app (op (Over.mk (𝟙 W)))
    (1 : ((Stacks.SheafOfModules.Tensor.ringSheaf (X.over W).O).obj.obj
      (op (Over.mk (𝟙 W)))))) h2).trans rfl

omit [HasSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [∀ W : X.C, HasSheafify (X.J.over W) AddCommGrpCat.{u}]
  [∀ W : X.C, (X.J.over W).WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- **A map of complexes out of the structure sheaf of the localized site is determined by its
`sliceCocycleOf`.** -/
theorem sliceUnitComplex_hom_ext {W : X.C} {L : Complexes (X.over W).O}
    {φ ψ : sliceUnitComplex W ⟶ L} (h : sliceCocycleOf φ = sliceCocycleOf ψ) : φ = ψ := by
  refine HomologicalComplex.from_single_hom_ext ?_
  refine (cancel_epi (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
    (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf (X.over W).O))).inv).1 ?_
  exact unitHom_ext_of_terminal h

omit [HasSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- `sliceCocycleHom` sends `1` to the section it was built from. -/
theorem sliceCocycleOf_sliceCocycleHom (W : X.C) (A : Complexes X.O)
    (t : (A.X 0).val.obj (op W)) (ht : (A.d 0 1).val.app (op W) t = 0) :
    sliceCocycleOf (sliceCocycleHom W A t ht) = t :=
  SheafOfModules.cocycleOfOver_cocycleHomOver (Stacks.SheafOfModules.Tensor.ringSheaf X.O) A W t ht

/-- The map of complexes out of the structure sheaf of the localized site attached to a
degree-zero cocycle section over the final object of a complex on the localized site. -/
def sliceUnitHom {W : X.C} (L : Complexes (X.over W).O)
    (s : (L.X 0).val.obj (op (Over.mk (𝟙 W))))
    (hs : (L.d 0 1).val.app (op (Over.mk (𝟙 W))) s = 0) :
    sliceUnitComplex W ⟶ L :=
  HomologicalComplex.mkHomFromSingle (unitHomOfTerminal _ s) (fun k hk => by
    obtain rfl : k = 1 := by simpa using hk.symm
    refine unitHom_ext_of_terminal ?_
    change (L.d 0 1).val.app (op (Over.mk (𝟙 W))) ((unitHomOfTerminal _ s).val.app
      (op (Over.mk (𝟙 W)))
        (1 : ((Stacks.SheafOfModules.Tensor.ringSheaf (X.over W).O).obj.obj
          (op (Over.mk (𝟙 W)))))) = _
    rw [unitHomOfTerminal_val_app, hs]
    rfl)

omit [HasSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [∀ W : X.C, HasSheafify (X.J.over W) AddCommGrpCat.{u}]
  [∀ W : X.C, (X.J.over W).WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- `sliceUnitHom` sends `1` to the section it was built from. -/
theorem sliceCocycleOf_sliceUnitHom {W : X.C} (L : Complexes (X.over W).O)
    (s : (L.X 0).val.obj (op (Over.mk (𝟙 W))))
    (hs : (L.d 0 1).val.app (op (Over.mk (𝟙 W))) s = 0) :
    sliceCocycleOf (sliceUnitHom L s hs) = s := by
  have h : (sliceUnitHom L s hs).f 0 = (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
      (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf (X.over W).O))).hom ≫
        unitHomOfTerminal _ s :=
    HomologicalComplex.mkHomFromSingle_f _ _
  rw [sliceCocycleOf, h, Iso.inv_hom_id_assoc]
  exact unitHomOfTerminal_val_app _ s

/-- **The tensor isomorphism of an invertible object, read on the localized site.** For K-flat
`ℳ`, `𝒩` and `γ : Q(Tot(ℳ ⊗ 𝒩)) ≅ Q(O[0])` in `D(O)`, the restrictions of `ℳ` and `𝒩` to `C/W`
satisfy `Q(ℳ|_W) ⊗ Q(𝒩|_W) ≅ 𝟙` in `D(O|_W)`: the comparison of Stacks 0FPT, the chain-level
identification of `Tot(ℳ ⊗ 𝒩)|_W` with `Tot(ℳ|_W ⊗ 𝒩|_W)`, the restriction of `γ`, and the
identification of `O[0]|_W` with the structure sheaf of `C/W` in degree zero. -/
def sliceTensorIsoUnit (W : X.C) (Mc Nc : Complexes X.O) (hM : KFlat X.O Mc)
    (hN : KFlat X.O Nc)
    (γ : DerivedCategory.Q.obj (Mc ⊗ Nc : Complexes X.O) ≅
      DerivedCategory.Q.obj X.structureSheafComplex) :
    letI := derivedMonoidal (X.over W).O
    DerivedCategory.Q.obj (restrictMod Mc W) ⊗ DerivedCategory.Q.obj (restrictMod Nc W) ≅
      𝟙_ (Stacks.SheafOfModules.DerivedMonoidal.DerivedModules (X.over W).O) :=
  letI := derivedMonoidal (X.over W).O
  (symmetricMonoidalDerived (X.over W).O).comparison _ _
      (Stacks.Cohomology.DerivedRestriction.kFlat_restriction X W Mc hM)
      (Stacks.Cohomology.DerivedRestriction.kFlat_restriction X W Nc hN) ≪≫
    DerivedCategory.Q.mapIso (sliceTensorIso W Mc Nc).symm ≪≫
    ((ovF X W).mapDerivedCategoryFactors.app (Mc ⊗ Nc : Complexes X.O)).symm ≪≫
    (ovF X W).mapDerivedCategory.mapIso γ ≪≫
    (ovF X W).mapDerivedCategoryFactors.app X.structureSheafComplex ≪≫
    DerivedCategory.Q.mapIso (sliceUnitComplexIso W) ≪≫
    (symmetricMonoidalDerived (X.over W).O).unitIso.symm

/-- **The inverse of `sliceTensorIsoUnit` at chain level.** If the restriction of `γ⁻¹` to `C/W`
is the class of the map of complexes attached to a degree-zero cocycle section `t` of
`Tot(ℳ ⊗ 𝒩)` over `W`, then the inverse of `sliceTensorIsoUnit` is the class of that map
followed by the chain-level identification `Tot(ℳ ⊗ 𝒩)|_W ≅ Tot(ℳ|_W ⊗ 𝒩|_W)`. -/
theorem sliceTensorIsoUnit_inv (W : X.C) (Mc Nc : Complexes X.O) (hM : KFlat X.O Mc)
    (hN : KFlat X.O Nc)
    (γ : DerivedCategory.Q.obj (Mc ⊗ Nc : Complexes X.O) ≅
      DerivedCategory.Q.obj X.structureSheafComplex)
    (t : ((Mc ⊗ Nc : Complexes X.O).X 0).val.obj (op W))
    (ht : ((Mc ⊗ Nc : Complexes X.O).d 0 1).val.app (op W) t = 0)
    (hβ : (ovF X W).mapDerivedCategory.map γ.inv ≫
        (ovF X W).mapDerivedCategoryFactors.hom.app (Mc ⊗ Nc : Complexes X.O) =
      (ovF X W).mapDerivedCategoryFactors.hom.app X.structureSheafComplex ≫
        DerivedCategory.Q.map ((sliceUnitComplexIso W).hom ≫ sliceCocycleHom W _ t ht)) :
    letI := derivedMonoidal (X.over W).O
    (sliceTensorIsoUnit W Mc Nc hM hN γ).inv =
      (symmetricMonoidalDerived (X.over W).O).unitIso.hom ≫
        DerivedCategory.Q.map (sliceCocycleHom W _ t ht ≫ (sliceTensorIso W Mc Nc).hom) ≫
        ((symmetricMonoidalDerived (X.over W).O).comparison _ _
          (Stacks.Cohomology.DerivedRestriction.kFlat_restriction X W Mc hM)
          (Stacks.Cohomology.DerivedRestriction.kFlat_restriction X W Nc hN)).inv := by
  let := derivedMonoidal (X.over W).O
  have hR : (ovF X W).mapDerivedCategoryFactors.inv.app X.structureSheafComplex ≫
        (ovF X W).mapDerivedCategory.map γ.inv ≫
          (ovF X W).mapDerivedCategoryFactors.hom.app (Mc ⊗ Nc : Complexes X.O) =
      DerivedCategory.Q.map ((sliceUnitComplexIso W).hom ≫ sliceCocycleHom W _ t ht) := by
    rw [hβ]
    exact Iso.inv_hom_id_app_assoc _ _ _
  have h1 : (sliceTensorIsoUnit W Mc Nc hM hN γ).inv =
      (((((((symmetricMonoidalDerived (X.over W).O).unitIso.hom ≫
        DerivedCategory.Q.map (sliceUnitComplexIso W).inv) ≫
        (ovF X W).mapDerivedCategoryFactors.inv.app X.structureSheafComplex) ≫
        (ovF X W).mapDerivedCategory.map γ.inv) ≫
        (ovF X W).mapDerivedCategoryFactors.hom.app (Mc ⊗ Nc : Complexes X.O)) ≫
        DerivedCategory.Q.map (sliceTensorIso W Mc Nc).hom) ≫
        ((symmetricMonoidalDerived (X.over W).O).comparison _ _
          (Stacks.Cohomology.DerivedRestriction.kFlat_restriction X W Mc hM)
          (Stacks.Cohomology.DerivedRestriction.kFlat_restriction X W Nc hN)).inv) := rfl
  rw [h1]
  simp only [Category.assoc]
  rw [reassoc_of% hR, ← Functor.map_comp_assoc, ← Functor.map_comp_assoc, Iso.inv_hom_id_assoc]

/-- **Over `W`, the restriction of an invertible object is a retract of every complex through
which the cocycle of its tensor inverse lifts.** Let `ℳ`, `𝒩` be K-flat and
`γ : Q(Tot(ℳ ⊗ 𝒩)) ≅ Q(O[0])`, and suppose that over `W` the restriction of `γ⁻¹` is the class of
the map of complexes attached to a degree-zero cocycle section `t` of `Tot(ℳ ⊗ 𝒩)` over `W`. Let
`ι : 𝒦 ⟶ ℳ|_W` be a map of complexes on the localized site `C/W` such that `ι ▷ 𝒩|_W` is a
monomorphism in degree one, and let `s` be a degree-zero section of `Tot(𝒦 ⊗ 𝒩|_W)` over the
final object of `C/W` carried by `ι ▷ 𝒩|_W` to the image of `t`. Then `Q(ℳ|_W)` is a retract of
`Q(𝒦)` in `D(O|_W)`. -/
theorem nonempty_retract_restrictMod_of_tensorIsoUnit (W : X.C) (Mc Nc : Complexes X.O)
    (hM : KFlat X.O Mc) (hN : KFlat X.O Nc)
    (γ : DerivedCategory.Q.obj (Mc ⊗ Nc : Complexes X.O) ≅
      DerivedCategory.Q.obj X.structureSheafComplex)
    (t : ((Mc ⊗ Nc : Complexes X.O).X 0).val.obj (op W))
    (ht : ((Mc ⊗ Nc : Complexes X.O).d 0 1).val.app (op W) t = 0)
    (hβ : (ovF X W).mapDerivedCategory.map γ.inv ≫
        (ovF X W).mapDerivedCategoryFactors.hom.app (Mc ⊗ Nc : Complexes X.O) =
      (ovF X W).mapDerivedCategoryFactors.hom.app X.structureSheafComplex ≫
        DerivedCategory.Q.map ((sliceUnitComplexIso W).hom ≫ sliceCocycleHom W _ t ht))
    (K : Complexes (X.over W).O) (ι : K ⟶ restrictMod Mc W)
    [Mono ((ι ▷ restrictMod Nc W : (K ⊗ restrictMod Nc W : Complexes (X.over W).O) ⟶
      (restrictMod Mc W ⊗ restrictMod Nc W : Complexes (X.over W).O)).f 1)]
    (s : ((K ⊗ restrictMod Nc W : Complexes (X.over W).O).X 0).val.obj (op (Over.mk (𝟙 W))))
    (hs : ((ι ▷ restrictMod Nc W : (K ⊗ restrictMod Nc W : Complexes (X.over W).O) ⟶
        (restrictMod Mc W ⊗ restrictMod Nc W : Complexes (X.over W).O)).f 0).val.app
          (op (Over.mk (𝟙 W))) s =
      ((sliceTensorIso W Mc Nc).hom.f 0).val.app (op (Over.mk (𝟙 W)))
        (sliceCocycleOf (sliceCocycleHom W _ t ht))) :
    Nonempty (Retract (DerivedCategory.Q.obj (restrictMod Mc W)) (DerivedCategory.Q.obj K)) := by
  let := derivedMonoidal (X.over W).O
  let := derivedSymmetric (X.over W).O
  obtain ⟨Θ, hΘ⟩ := exists_iso_whiskerRight_comp (X.over W).O ι
    (Stacks.Cohomology.DerivedRestriction.kFlat_restriction X W Mc hM)
    (Stacks.Cohomology.DerivedRestriction.kFlat_restriction X W Nc hN)
  -- `s` is a cocycle, because its image is.
  have hsd : ((K ⊗ restrictMod Nc W : Complexes (X.over W).O).d 0 1).val.app
      (op (Over.mk (𝟙 W))) s = 0 := by
    refine SheafOfModules.d_zero_of_mono_f_one
      (ι ▷ restrictMod Nc W : (K ⊗ restrictMod Nc W : Complexes (X.over W).O) ⟶ _) s ?_
    rw [hs, ← sliceCocycleOf_comp]
    exact sliceCocycleOf_d _
  have hc₀ : sliceUnitHom _ s hsd ≫ (ι ▷ restrictMod Nc W) =
      sliceCocycleHom W _ t ht ≫ (sliceTensorIso W Mc Nc).hom := by
    refine sliceUnitComplex_hom_ext ?_
    rw [sliceCocycleOf_comp, sliceCocycleOf_comp, sliceCocycleOf_sliceUnitHom, hs]
  refine nonempty_retract_of_tensorIsoUnit_inv_eq (sliceTensorIsoUnit W Mc Nc hM hN γ)
    ((β_ _ _).hom ≫ (sliceTensorIsoUnit W Mc Nc hM hN γ).hom) (DerivedCategory.Q.map ι)
    ((symmetricMonoidalDerived (X.over W).O).unitIso.hom ≫
      DerivedCategory.Q.map (sliceUnitHom _ s hsd) ≫ Θ.hom) ?_
  refine Eq.trans ?_ (sliceTensorIsoUnit_inv W Mc Nc hM hN γ t ht hβ).symm
  refine (Category.assoc _ _ _).trans (congrArg (_ ≫ ·) ?_)
  refine (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) hΘ).trans ?_)
  refine (Category.assoc _ _ _).symm.trans (congrArg (· ≫ _) ?_)
  exact (Functor.map_comp _ _ _).symm.trans (congrArg _ hc₀)

end AlgebraicGeometry.RingedSite.InvertibleDerived

end
