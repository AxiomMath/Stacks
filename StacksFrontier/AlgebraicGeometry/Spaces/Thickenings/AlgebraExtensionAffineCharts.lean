module

public import StacksFrontier.AlgebraicGeometry.Spaces.AffineChartSurjectivityFromDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineChartsHaveEnoughObjects
public import StacksFrontier.AlgebraicGeometry.Spaces.SheafOfDifferentials
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.SquareZeroExtensionAffineCharts
public import StacksFrontier.Deformation.AlgebraExtension.InducedKernelMap
public import StacksFrontier.AlgebraicGeometry.Size.CoveringsSupplement
public import StacksFrontier.AlgebraicGeometry.Spaces.Category
public import StacksFrontier.AlgebraicGeometry.Spaces.Points
public import StacksFrontier.Topology.Dimension.KrullSupplement

/-!
# Extensions of the étale structure sheaf with quasi-coherent ideal, over affine charts

Let `X ⟶ Y` be a morphism of algebraic spaces and `0 → ℳ → 𝒪' → 𝒪_X → 0` an extension of
`f⁻¹𝒪_Y`-algebras on the small étale site of `X` (`Deformation.AlgebraExtension`) whose ideal `ℳ`
is quasi-coherent. Such an extension is the data of Stacks 05ZT
(`AlgebraicGeometry.Space.SquareZeroExtension`), so over every affine étale chart `W` the
reduction `𝒪'(W) ⟶ 𝒪_X(W)` is surjective (`H¹(W, ℳ) = 0`, Stacks 03F8).

The same holds for a homomorphism `h : 𝒪'_P ⟶ 𝒪'_Q` of the middle terms of two such extensions
over `𝒪_X` which is locally surjective: the map of ideals it induces is an epimorphism of
quasi-coherent modules, hence surjective over `W` (Stacks 03DW), and the five lemma on sections
gives surjectivity of `h` over `W`. This is the argument of the proof of
[Stacks Project, Tag 0D3X] that the transition maps `𝒪_{X_{n+1}}(W) ⟶ 𝒪_{X_n}(W)` are surjective
over affine `W`, which makes `lim 𝒪_{X_n}` an extension of `𝒪_{X_1}`.

## Main definitions

* `AlgebraicGeometry.Space.SquareZeroExtension.ofAlgebraExtension`: the 05ZT data of an extension
  with quasi-coherent ideal.

## Main results

* `AlgebraicGeometry.Space.surjective_reduction_app_of_isQuasicoherentOnSite`: the reduction is
  surjective over affine charts.
* `AlgebraicGeometry.Space.surjective_extensionHom_app_of_isQuasicoherentOnSite`: so is a locally
  surjective homomorphism of middle terms over `𝒪_X`.
* `AlgebraicGeometry.Space.isLocallySurjective_of_surjective_app_isAffineChart`: a morphism of
  sheaves of rings on the small étale site which is surjective over affine charts is locally
  surjective.

## References

* [Stacks Project, Tag 05ZT](https://stacks.math.columbia.edu/tag/05ZT)
* [Stacks Project, Tag 03F8](https://stacks.math.columbia.edu/tag/03F8)
* [Stacks Project, Tag 03DW](https://stacks.math.columbia.edu/tag/03DW)
* [Stacks Project, Tag 0D3X](https://stacks.math.columbia.edu/tag/0D3X)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {X Y : AlgebraicSpaces B S hS}

/-- **The 05ZT data of an extension with quasi-coherent ideal.** An extension of
`f⁻¹𝒪_Y`-algebras of `𝒪_X` by a quasi-coherent `𝒪_X`-module is a square-zero extension of the
structure sheaf of `X` relative to `f`. -/
def SquareZeroExtension.ofAlgebraExtension (f : X ⟶ Y)
    {M : SheafOfModules.{u} ((sheafCompose (SmallEtale.topology B S hS X.1)
      (forget₂ CommRingCat.{u} RingCat.{u})).obj (smallEtaleRingedTopos B S hS X).O)}
    (P : Deformation.AlgebraExtension (J := SmallEtale.topology B S hS X.1)
      (structureSharpInverseImage B S hS f) M) (hM : M.IsQuasicoherentOnSite) :
    SquareZeroExtension B S hS f where
  A := P.extension
  π := P.reduction
  locallySurjective_π := P.locallySurjective
  toBase := P.algebraMap
  toBase_π := P.algebraMap_reduction
  I := M
  quasicoherent := hM
  ι U := (P.kernelInclusion.val.app U).hom.toAddMonoidHom
  naturality g x := P.incl_naturality g x
  mem_kernel U x := P.kernelZero U x
  exact_kernel U a ha := P.kernelUniversal U a ha
  smul_lift _ a x := (P.mul_incl a x).symm
  square_zero _ x y := P.incl_mul_incl x y

/-- **The reduction of an extension with quasi-coherent ideal is surjective over every affine
étale chart**: it is the surjection of the 05ZT data
`AlgebraicGeometry.Space.SquareZeroExtension.ofAlgebraExtension`, whose kernel has vanishing
first Čech cohomology on the finite affine coverings of an affine chart (Stacks 03F8). -/
theorem surjective_reduction_app_of_isQuasicoherentOnSite (f : X ⟶ Y)
    {M : SheafOfModules.{u} ((sheafCompose (SmallEtale.topology B S hS X.1)
      (forget₂ CommRingCat.{u} RingCat.{u})).obj (smallEtaleRingedTopos B S hS X).O)}
    (P : Deformation.AlgebraExtension (J := SmallEtale.topology B S hS X.1)
      (structureSharpInverseImage B S hS f) M) (hM : M.IsQuasicoherentOnSite)
    (W : SmallEtale B S hS X.1) (hW : IsAffineChart B S hS X.1 W) :
    Function.Surjective (P.reduction.hom.app (op W)) :=
  (SquareZeroExtension.ofAlgebraExtension f P hM).surjective_π_app_of_isAffineChart W hW

/-- **A locally surjective homomorphism of the middle terms of two extensions with
quasi-coherent ideals, over `𝒪_X`, is surjective over every affine étale chart.** The map of
ideals it induces is locally surjective, hence an epimorphism of quasi-coherent modules, hence
surjective over an affine chart (Stacks 03DW); the reduction of the source is surjective over an
affine chart; and the five lemma on sections concludes. -/
theorem surjective_extensionHom_app_of_isQuasicoherentOnSite (f : X ⟶ Y)
    {A' : Sheaf (SmallEtale.topology B S hS X.1) CommRingCat.{u}}
    {a' : A' ⟶ (smallEtaleRingedTopos B S hS X).O}
    {M N : SheafOfModules.{u} ((sheafCompose (SmallEtale.topology B S hS X.1)
      (forget₂ CommRingCat.{u} RingCat.{u})).obj (smallEtaleRingedTopos B S hS X).O)}
    (P : Deformation.AlgebraExtension (J := SmallEtale.topology B S hS X.1)
      (structureSharpInverseImage B S hS f) M)
    (Q : Deformation.AlgebraExtension (J := SmallEtale.topology B S hS X.1) a' N)
    (hM : M.IsQuasicoherentOnSite) (hN : N.IsQuasicoherentOnSite)
    (h : P.extension ⟶ Q.extension) (hh : h ≫ Q.reduction = P.reduction)
    (hs : Presheaf.IsLocallySurjective (SmallEtale.topology B S hS X.1) h.hom)
    (W : SmallEtale B S hS X.1) (hW : IsAffineChart B S hS X.1 W) :
    Function.Surjective (h.hom.app (op W)) :=
  Deformation.AlgebraExtension.surjective_hom_app_of_surjective P Q h hh
    (surjective_reduction_app_of_isQuasicoherentOnSite f P hM W hW)
    (surjective_val_app_of_epi_of_isQuasicoherentOnSite (hF := X.2) _
      (Deformation.AlgebraExtension.epi_inducedKernelMap P Q h hh hs) hM hN W hW)

/-- **Surjectivity over affine charts is local surjectivity.** A morphism of sheaves of
commutative rings on the small étale site of `X` which is surjective on the sections over every
affine étale chart is locally surjective: the affine charts cover every chart. -/
theorem isLocallySurjective_of_surjective_app_isAffineChart
    {F G : Sheaf (SmallEtale.topology B S hS X.1) CommRingCat.{u}} (φ : F ⟶ G)
    (hφ : ∀ W : SmallEtale B S hS X.1, IsAffineChart B S hS X.1 W →
      Function.Surjective (φ.hom.app (op W))) :
    Presheaf.IsLocallySurjective (SmallEtale.topology B S hS X.1) φ.hom where
  imageSieve_mem {U} s := by
    obtain ⟨I, Ui, f, hcov, haff⟩ := hasEnoughObjects_isAffineChart B S hS X.1 U
    refine (SmallEtale.topology B S hS X.1).superset_covering ?_ hcov
    rintro V g ⟨W, k, _, ⟨i⟩, rfl⟩
    obtain ⟨t, ht⟩ := hφ (Ui i) (haff i) (G.obj.map (f i).op s)
    exact (Presheaf.imageSieve φ.hom s).downward_closed ⟨t, ht⟩ k

end AlgebraicGeometry.Space

end
