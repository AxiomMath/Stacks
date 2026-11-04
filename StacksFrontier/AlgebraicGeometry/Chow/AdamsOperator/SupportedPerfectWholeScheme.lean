module

public import StacksFrontier.AlgebraicGeometry.Perfect.BoundedLocallyFreeComplexes.CanonicalFunctor
public import StacksFrontier.AlgebraicGeometry.Perfect.KGroups.Basic
public import StacksFrontier.CategoryTheory.Triangulated.KGroup.Basic
public import StacksFrontier.Topology.Sheaves.Cohomology.PerfectComplexes.TriangulatedSubcategory
public import StacksCore.Tactic.StacksAttribute

/-!
# Perfect complexes supported on the whole scheme

Every perfect object of the derived category of a scheme is supported on the whole scheme, so
taking the closed subscheme to be `X` itself, with the identity closed immersion, the category of
perfect complexes supported on it is the category `D_perf(O_X)` of all perfect complexes.
Consequently its `K`-group is the Grothendieck group `K_0(X) = K_0(D_perf(O_X))` of the scheme.
This is the identification which makes the Chern classes and the Chern character of chapter 42,
constructed in general for a closed subscheme, specialize to maps out of `K_0(X)`.

## Main definitions

* `AlgebraicGeometry.supportedPerfectKZeroEquiv` — the canonical additive isomorphism from the
  `K`-group of perfect complexes supported on the whole scheme to `K_0(D_perf(O_X))`.

## Main results

* `AlgebraicGeometry.supportedPerfectProperty_id_eq_isPerfect` — for the identity immersion the
  supported-perfect object condition is perfectness.
* `AlgebraicGeometry.isTriangulated_supportedPerfect_id` — hence that condition cuts out a
  triangulated subcategory, which is what makes its `K`-group available.
* `AlgebraicGeometry.supportedPerfectDerivedCategory_id` — the two full subcategories are equal.
* `AlgebraicGeometry.supportedPerfectKZeroEquiv_cls` — the isomorphism on classes of objects.

## Implementation notes

The support condition is containment in `Set.range i.base`, which for the identity immersion is
the whole space, so the condition is vacuous and the two object properties agree. The
quasi-compactness and local finite-type assumptions of the source play no role in this
identification, and neither does a choice of base scheme.

Perfectness is spelled `AlgebraicGeometry.RingedSpace.IsPerfect` in the supported category and
`Stacks.Cohomology.PerfectComplexes.IsPerfect` in `D_perf(O_X)`; the two unfold to the same
condition. Likewise the ambient category is written over `StrictlyPerfect.OXMod X.toRingedSpace`
in the first case and over `X.Modules` in the second, and these are the same category.

The isomorphism of `K`-groups is induced by the two mutually inverse inclusions of full
subcategories, which are triangulated functors because each becomes the inclusion of a
triangulated subcategory after composing with the other inclusion. It is *not* obtained by
transporting along the equality of categories, because the two sides carry their pretriangulated
structures through different object properties.

## References

* [Stacks Project, Tag 0FEU](https://stacks.math.columbia.edu/tag/0FEU)
-/

@[expose] public section

open CategoryTheory StrictlyPerfect Stacks.Perfect.BoundedLocallyFreeComplexes

universe u d

namespace AlgebraicGeometry

/-- For the identity closed immersion the supported-perfect object condition is perfectness: the
support of every cohomology sheaf is contained in the whole space. -/
theorem supportedPerfectProperty_id_eq_isPerfect (X : Scheme.{u})
    [HasDerivedCategory.{d} (OXMod.{u, u} X.toRingedSpace)] :
    (show ObjectProperty (DerivedCategory (OXMod.{u, u} X.toRingedSpace)) from
      fun K => RingedSpace.IsPerfect K ∧
        ∀ n : ℤ, SheafOfModules.supp
          ((DerivedCategory.homologyFunctor (OXMod.{u, u} X.toRingedSpace) n).obj K) ⊆
            Set.range (𝟙 X : X ⟶ X).base)
      = (Stacks.Cohomology.PerfectComplexes.IsPerfect :
          ObjectProperty (DerivedCategory (OXMod.{u, u} X.toRingedSpace))) := by
  ext K
  simp
  rfl

/-- Perfect complexes supported on the whole scheme form a triangulated subcategory of the
derived category, because they are exactly the perfect complexes. -/
@[sga "6 I 5.8.4" "5.8.4 a)"]
instance isTriangulated_supportedPerfect_id (X : Scheme.{u})
    [HasDerivedCategory.{d} (OXMod.{u, u} X.toRingedSpace)] :
    ObjectProperty.IsTriangulated
      (show ObjectProperty (DerivedCategory (OXMod.{u, u} X.toRingedSpace)) from
        fun K => RingedSpace.IsPerfect K ∧
          ∀ n : ℤ, SheafOfModules.supp
            ((DerivedCategory.homologyFunctor (OXMod.{u, u} X.toRingedSpace) n).obj K) ⊆
              Set.range (𝟙 X : X ⟶ X).base) := by
  rw [supportedPerfectProperty_id_eq_isPerfect X]
  exact Stacks.Cohomology.PerfectTriangulatedSubcategory.isTriangulated_isPerfect X.toRingedSpace

section

attribute [local instance] HasDerivedCategory.standard

/-- **Stacks 0FEU.** Perfect objects of the derived category supported on the whole scheme are
exactly the perfect objects: `D_{X, perf}(O_X) = D_perf(O_X)`. -/
@[stacks 0FEU "supported_perfect"]
theorem supportedPerfectDerivedCategory_id (X : Scheme.{u}) :
    supportedPerfectDerivedCategory (𝟙 X) = PerfectDerivedCategory X := by
  show ObjectProperty.FullSubcategory _ = _
  congr 1
  ext K
  simp
  rfl

/-- **Stacks 0FEU.** The `K`-group of perfect complexes supported on the whole scheme is the
Grothendieck group `K_0(X) = K_0(D_perf(O_X))` of the scheme. -/
@[stacks 0FEU "k_group"]
noncomputable def supportedPerfectKZeroEquiv (X : Scheme.{u}) :
    Pretriangulated.K0 (supportedPerfectDerivedCategory (𝟙 X)) ≃+
      Pretriangulated.K0 (PerfectDerivedCategory X) := by
  let P : ObjectProperty (DerivedCategory (OXMod.{u, u} X.toRingedSpace)) :=
    fun K => RingedSpace.IsPerfect K ∧ ∀ n : ℤ,
      SheafOfModules.supp
        ((DerivedCategory.homologyFunctor (OXMod.{u, u} X.toRingedSpace) n).obj K) ⊆
          Set.range (𝟙 X : X ⟶ X).base
  let Q : ObjectProperty (DerivedCategory (OXMod.{u, u} X.toRingedSpace)) :=
    fun K => Stacks.Cohomology.PerfectComplexes.IsPerfect K
  let : P.IsTriangulated := isTriangulated_supportedPerfect_id X
  let : Q.IsTriangulated :=
    Stacks.Cohomology.PerfectTriangulatedSubcategory.isTriangulated_isPerfect X.toRingedSpace
  let : P.IsStableUnderShift ℤ := inferInstance
  let : Q.IsStableUnderShift ℤ := inferInstance
  have hPQ : P ≤ Q := fun _ h ↦ h.1
  have hQP : Q ≤ P := fun _ h ↦ ⟨h, by intro n; simp⟩
  let F : P.FullSubcategory ⥤ Q.FullSubcategory :=
    Q.lift P.ι fun K ↦ hPQ K.obj K.property
  let G : Q.FullSubcategory ⥤ P.FullSubcategory :=
    P.lift Q.ι fun K ↦ hQP K.obj K.property
  have eF : F ⋙ Q.ι ≅ P.ι :=
    ObjectProperty.liftCompιIso Q P.ι fun K ↦ hPQ K.obj K.property
  have eG : G ⋙ P.ι ≅ Q.ι :=
    ObjectProperty.liftCompιIso P Q.ι fun K ↦ hQP K.obj K.property
  let : F.CommShift ℤ := Functor.CommShift.ofComp eF ℤ
  let : G.CommShift ℤ := Functor.CommShift.ofComp eG ℤ
  have : NatTrans.CommShift eF.hom ℤ := Functor.CommShift.ofComp_compatibility eF ℤ
  have : NatTrans.CommShift eG.hom ℤ := Functor.CommShift.ofComp_compatibility eG ℤ
  let : F.IsTriangulated := (Functor.isTriangulated_iff_comp_right eF).2 inferInstance
  let : G.IsTriangulated := (Functor.isTriangulated_iff_comp_right eG).2 inferInstance
  let f := Pretriangulated.K0.map F
  let g := Pretriangulated.K0.map G
  have hfg : g.comp f = AddMonoidHom.id _ := by
    apply Pretriangulated.K0.hom_ext
    intro K
    simp only [f, g, AddMonoidHom.comp_apply, Pretriangulated.K0.map_cls]
    congr 1
  have hgf : f.comp g = AddMonoidHom.id _ := by
    apply Pretriangulated.K0.hom_ext
    intro K
    simp only [f, g, AddMonoidHom.comp_apply, Pretriangulated.K0.map_cls]
    congr 1
  have hleft : Function.LeftInverse g f := fun x ↦ by
    simpa [AddMonoidHom.comp_apply] using DFunLike.congr_fun hfg x
  have hright : Function.RightInverse g f := fun y ↦ by
    simpa [AddMonoidHom.comp_apply] using DFunLike.congr_fun hgf y
  exact AddEquiv.ofBijective f ⟨hleft.injective, hright.surjective⟩

/-- **Stacks 0FEU.** The identification of `K`-groups takes the class of a perfect complex
supported on the whole scheme to the class of the same complex in `K_0(D_perf(O_X))`. -/
@[stacks 0FEU "k_group"]
theorem supportedPerfectKZeroEquiv_cls (X : Scheme.{u})
    (K : supportedPerfectDerivedCategory (𝟙 X)) :
    supportedPerfectKZeroEquiv X (Pretriangulated.K0.cls K) =
      Pretriangulated.K0.cls (⟨K.obj, K.property.1⟩ : PerfectDerivedCategory X) :=
  rfl

end

end AlgebraicGeometry

end
