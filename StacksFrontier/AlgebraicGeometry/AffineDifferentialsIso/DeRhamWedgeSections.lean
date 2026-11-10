module

public import StacksFrontier.AlgebraicGeometry.AffineDifferentialsIso.DeRhamSections
public import StacksFrontier.AlgebraicGeometry.AffineDifferentialsIso.TildeExteriorProduct
public import StacksFrontier.AlgebraicGeometry.DeRham.Functoriality
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ExteriorPowerProdSheaf

/-!
# The de Rham differential of a morphism of affine schemes, on a wedge of global sections

Let `φ : R ⟶ A` be a morphism of commutative rings. The comparison
`Stacks.AlgebraicGeometry.AffineDifferentialsIso.differentialFormsSectionsIso` identifies
`⋀^p_A Ω[A⁄R]` with the global relative differential `p`-forms of `Spec φ` in every degree, and
says nothing about the de Rham differential. This file computes the comparison on the wedges
`d a₁ ∧ ⋯ ∧ d a_p` which span `⋀^p_A Ω[A⁄R]`, and reads the de Rham differential of the relative
de Rham complex on the image of such a wedge.

## Main results

* `AlgebraicGeometry.Scheme.Hom.deRhamComplex_d_homogeneousProdLeft`: **the de Rham rule of
  `Ω^•_{X/S}`, in every degree**, for an arbitrary morphism of schemes: the differential of the
  relative de Rham complex carries `b · (d c₁ ∧ ⋯ ∧ d c_p)` to `d b ∧ d c₁ ∧ ⋯ ∧ d c_p`. This is
  the library's `DeRhamDifferential.differential_smul_homogeneousProdLeft`, read on the arrows of
  the
  complex of a morphism of schemes.
* `Stacks.AlgebraicGeometry.AffineDifferentialsIso.differentialFormsSectionsIso_ιMulti`: the
  degreewise comparison carries a wedge `m₁ ∧ ⋯ ∧ m_p` of Kähler differentials to the ordered
  product of the degree-one forms attached to the `m_i`.
* `Stacks.AlgebraicGeometry.AffineDifferentialsIso.differentialFormsSectionsIso_ιMulti_d`: the
  same for a wedge of universal differentials `d a₁ ∧ ⋯ ∧ d a_p`, where the degree-one forms are
  the exact one-forms `d` of the global sections corresponding to the `a_i`.
* `Stacks.AlgebraicGeometry.AffineDifferentialsIso.deRhamComplex_d_sectionsIso`: **the de Rham
  differential of `Spec φ`, read on global sections through the degreewise comparison, obeys the
  rule `d (a₀ · d a₁ ∧ ⋯ ∧ d a_p) = d a₀ ∧ d a₁ ∧ ⋯ ∧ d a_p` in every degree.**

## Implementation notes

The one input that makes every degree available is
`AlgebraicGeometry.tildeExteriorPowerIso_hom_ιMulti`: the comparison of Tag 01I8 carries the
global section of `(⋀^p_A M)~` attached to a wedge to the ordered product of the degree-one
generators of `⋀(M~)`. The second factor of `differentialFormsTildeIso` is the exterior power of
`tildeKaehlerIso` in a fixed degree, and a map of exterior powers induced by a morphism of
sheaves of modules carries ordered products of degree-one sections to ordered products
(`SheafOfModules.GradedAlgebra.UnitalHom.app_homogeneousProd_comp`, applied to the
characterizing equation `IsExteriorAlgebra.map_app_one`); the ordered product is written
left-handed, as the source writes it, and the transport-free right-handed spelling is reached by
`Stacks.GradedAlgebra.homogeneousProdLeft_eq_homogeneousProd`.

The de Rham rule itself is not re-proved and not restated from its `HEq` form: the transport-free
form is proved as
`AlgebraicGeometry.SheafOfModules.DeRhamDifferential.differential_smul_homogeneousProdLeft` in
`StacksFrontier.AlgebraicGeometry.DeRham.Functoriality`, and
`deRhamComplex_d_homogeneousProdLeft` only reads it on the arrows of
`AlgebraicGeometry.Scheme.Hom.deRhamComplex` and replaces its `Fin.cons b c` by a single tuple,
which is `Fin.cons_self_tail`.

The scalar `a₀ : A` acts on the global forms through `R ≅ Γ(Spec R, 𝒪)`, because
`AlgebraicGeometry.moduleSpecΓFunctor` restricts scalars along `Scheme.ΓSpecIso`; so the
`A`-linearity of the comparison turns `a₀ • ξ` into a multiple by the global section
`(Scheme.ΓSpecIso A).inv a₀`, which is the shape the sheaf-level rule consumes.

## References

* [Stacks Project, Tag 0FKM](https://stacks.math.columbia.edu/tag/0FKM)
* [Stacks Project, Tag 0FKQ](https://stacks.math.columbia.edu/tag/0FKQ)
* [Stacks Project, Tag 01I8](https://stacks.math.columbia.edu/tag/01I8)
* [Stacks Project, Tag 0FLW](https://stacks.math.columbia.edu/tag/0FLW)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme.Hom

section AnyScheme

variable {X S : Scheme.{u}} (f : X ⟶ S)

/-- **The de Rham rule of the relative de Rham complex, in every degree.** The differential of
`Ω^•_{X/S}` out of degree `p` carries the local section `b · (d c₁ ∧ ⋯ ∧ d c_p)` to the exact
wedge `d b ∧ d c₁ ∧ ⋯ ∧ d c_p` of degree `p + 1`.

This is
`AlgebraicGeometry.SheafOfModules.DeRhamDifferential.differential_smul_homogeneousProdLeft`, read
on the arrows of the relative de Rham complex of a morphism of schemes and with the `p + 1`
functions given as one tuple rather than as `Fin.cons`. -/
theorem deRhamComplex_d_homogeneousProdLeft (U : (X.Opens)ᵒᵖ) (p : ℕ)
    (c : Fin (p + 1) → ↥(X.sheaf.obj.obj U)) :
    ((deRhamComplex f).d p (p + 1)).val.app U
        (c 0 • (deRhamAlgebras f).exterior.toPresheafGradedAlgebra.homogeneousProdLeft U p
          fun i => SheafOfModules.exactOne (deRhamAlgebras f) U (c i.succ)) =
      (deRhamAlgebras f).exterior.toPresheafGradedAlgebra.homogeneousProdLeft U (p + 1)
        fun i => SheafOfModules.exactOne (deRhamAlgebras f) U (c i) := by
  rw [deRhamComplex_d]
  refine Eq.trans
    (SheafOfModules.DeRhamDifferential.differential_smul_homogeneousProdLeft
      (deRhamAlgebras f) (SheafOfModules.deRhamDifferential (deRhamAlgebras f)) p U (c 0)
      fun i : Fin p => c i.succ) ?_
  exact congrArg
    ((deRhamAlgebras f).exterior.toPresheafGradedAlgebra.homogeneousProdLeft U (p + 1))
    (funext fun i => congrArg (SheafOfModules.exactOne (deRhamAlgebras f) U)
      (congrFun (Fin.cons_self_tail c) i))

end AnyScheme

end AlgebraicGeometry.Scheme.Hom

namespace Stacks.AlgebraicGeometry.AffineDifferentialsIso

section DeRhamWedge

variable {R A : CommRingCat.{u}} (φ : R ⟶ A)

/-- **The degreewise comparison of differential forms, on a wedge of Kähler differentials.** It
carries `m₁ ∧ ⋯ ∧ m_p` to the ordered product, in the algebra of relative differential forms of
`Spec φ`, of the degree-one forms attached to the global differentials of the `m_i`.

Those wedges span `⋀^p_A Ω[A⁄R]`, so this determines the comparison in every degree. -/
theorem differentialFormsSectionsIso_ιMulti (p : ℕ)
    (m : Fin p → ↥(CommRingCat.KaehlerDifferential φ)) :
    (differentialFormsSectionsIso φ p).hom.hom (exteriorPower.ιMulti ↥A p m) =
      (Scheme.Hom.deRhamAlgebras (Spec.map φ)).exterior.toPresheafGradedAlgebra.homogeneousProdLeft
        (op ⊤) p fun i =>
          (Scheme.Hom.deRhamAlgebras (Spec.map φ)).exteriorGenerator.val.app (op ⊤)
            ((tildeKaehlerIso φ).hom.val.app (op ⊤)
              (tilde.toOpen (CommRingCat.KaehlerDifferential φ) ⊤ (m i))) := by
  have h : (differentialFormsSectionsIso φ p).hom.hom (exteriorPower.ιMulti ↥A p m) =
      (Scheme.Modules.exteriorPowerMap (tildeKaehlerIso φ).hom (p : ℤ)).val.app (op ⊤)
        ((tildeExteriorPowerIso A (CommRingCat.KaehlerDifferential φ) p).hom.val.app (op ⊤)
          (tilde.toOpen (ModuleCat.of ↥A ↥(⋀[↥A]^p ↥(CommRingCat.KaehlerDifferential φ))) ⊤
            (exteriorPower.ιMulti ↥A p m))) := rfl
  rw [h, tildeExteriorPowerIso_hom_ιMulti,
    Stacks.GradedAlgebra.homogeneousProdLeft_eq_homogeneousProd,
    Stacks.GradedAlgebra.homogeneousProdLeft_eq_homogeneousProd]
  exact SheafOfModules.GradedAlgebra.UnitalHom.app_homogeneousProd_comp
    ((Scheme.Modules.isExteriorAlgebra_exteriorAlgebra
        ((tilde.functor A).obj (CommRingCat.KaehlerDifferential φ))).map
      (Scheme.Modules.isExteriorAlgebra_exteriorAlgebra
        (Scheme.Hom.relativeDifferentials (Spec.map φ))) (tildeKaehlerIso φ).hom)
    (tildeKaehlerIso φ).hom
    (SheafOfModules.GradedAlgebra.IsExteriorAlgebra.map_app_one _ _ _) (op ⊤) p
    fun i => tilde.toOpen (CommRingCat.KaehlerDifferential φ) ⊤ (m i)

/-- **The comparison of sheaves of differentials, on a global section of the associated sheaf.**
It carries the global section attached to the universal differential of `a : A` to the universal
relative differential of the global section of `𝒪_{Spec A}` corresponding to `a`. -/
theorem tildeKaehlerIso_toOpen_d (a : ↥A) :
    (tildeKaehlerIso φ).hom.val.app (op ⊤)
        (tilde.toOpen (CommRingCat.KaehlerDifferential φ) ⊤
          (CommRingCat.KaehlerDifferential.d a)) =
      (Scheme.Hom.universalRelativeDerivation (Spec.map φ)).d ((Scheme.ΓSpecIso A).inv a) :=
  (congrArg (fun g : CommRingCat.KaehlerDifferential φ ⟶
        moduleSpecΓFunctor.obj (Scheme.Hom.relativeDifferentials (Spec.map φ)) =>
      g.hom (CommRingCat.KaehlerDifferential.d a))
    (toTildeΓ_comp_map_tildeKaehlerIso φ)).trans (sectionsIso_d φ a)

/-- **The degreewise comparison of differential forms, on a wedge of universal differentials.**
It carries `d a₁ ∧ ⋯ ∧ d a_p` to the ordered product of the exact one-forms of the global
sections of `𝒪_{Spec A}` corresponding to the `a_i`. -/
theorem differentialFormsSectionsIso_ιMulti_d (p : ℕ) (a : Fin p → ↥A) :
    (differentialFormsSectionsIso φ p).hom.hom
        (exteriorPower.ιMulti ↥A p fun i => CommRingCat.KaehlerDifferential.d (a i)) =
      (Scheme.Hom.deRhamAlgebras (Spec.map φ)).exterior.toPresheafGradedAlgebra.homogeneousProdLeft
        (op ⊤) p fun i =>
          SheafOfModules.exactOne (Scheme.Hom.deRhamAlgebras (Spec.map φ)) (op ⊤)
            ((Scheme.ΓSpecIso A).inv (a i)) :=
  (differentialFormsSectionsIso_ιMulti φ p _).trans
    (congrArg
      ((Scheme.Hom.deRhamAlgebras (Spec.map φ)).exterior.toPresheafGradedAlgebra.homogeneousProdLeft
        (op ⊤) p)
      (funext fun i => congrArg
        ((Scheme.Hom.deRhamAlgebras (Spec.map φ)).exteriorGenerator.val.app (op ⊤))
        (tildeKaehlerIso_toOpen_d φ (a i))))

/-- **The de Rham differential of `Spec φ`, read on global sections through the degreewise
comparison, in every degree.** On the image of the generator `a₀ · (d a₁ ∧ ⋯ ∧ d a_p)` of
`⋀^p_A Ω[A⁄R]` it is the image of `d a₀ ∧ d a₁ ∧ ⋯ ∧ d a_p`.

These generators span `⋀^p_A Ω[A⁄R]` over `R`, so this is the whole of the degree-`p` square of
[Stacks Project, Tag 0FLW], for every `p` — not only `p = 0`. -/
theorem deRhamComplex_d_sectionsIso (p : ℕ) (a : Fin (p + 1) → ↥A) :
    (((Spec.map φ).deRhamComplex).d p (p + 1)).val.app (op ⊤)
        ((differentialFormsSectionsIso φ p).hom.hom
          (a 0 • exteriorPower.ιMulti ↥A p fun i =>
            CommRingCat.KaehlerDifferential.d (a i.succ))) =
      (differentialFormsSectionsIso φ (p + 1)).hom.hom
        (exteriorPower.ιMulti ↥A (p + 1) fun i => CommRingCat.KaehlerDifferential.d (a i)) := by
  rw [map_smul, differentialFormsSectionsIso_ιMulti_d, differentialFormsSectionsIso_ιMulti_d]
  exact Scheme.Hom.deRhamComplex_d_homogeneousProdLeft (Spec.map φ) (op ⊤) p
    fun i => (Scheme.ΓSpecIso A).inv (a i)

end DeRhamWedge

end Stacks.AlgebraicGeometry.AffineDifferentialsIso

end
