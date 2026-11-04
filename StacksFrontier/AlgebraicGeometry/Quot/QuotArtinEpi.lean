module

public import StacksFrontier.AlgebraicGeometry.Spaces.InvertibleMapClosedFibre
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePullbackFlatDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.Properness.ProperClosedSubsetImage
public import StacksFrontier.AlgebraicGeometry.Spaces.Properness.ProperSupport
public import StacksFrontier.AlgebraicGeometry.Spaces.IdentityMorphismProperties
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparatedTfae
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteTypeProperties

/-!
# Surjectivity on a fibre meeting every closed set, for a target with proper support

A map `u : M ⟶ N` of quasi-coherent modules on an algebraic space `X` over `Y`, with `N` of
finite type and with support proper over `Y`, is surjective as soon as its restriction to the
fibre over a morphism `Y₀ ⟶ Y` meeting every nonempty closed subset of `|Y|` is. This is
`AlgebraicGeometry.Space.epi_of_epi_modulePullback_of_isPullback` with the universal closedness
of `X ⟶ Y` replaced by the properness of the support of the target, which is the form in which
the quotient maps of Grothendieck's existence theorem are shown to be surjective.

## Main results

* `AlgebraicGeometry.Space.epi_of_epi_modulePullback_of_hasProperSupport`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Space

universe u

attribute [local instance] pointTopology

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **A map whose target has proper support is surjective as soon as it is on a fibre meeting
every closed set.** -/
theorem epi_of_epi_modulePullback_of_hasProperSupport {X Y X₀ Y₀ : AlgebraicSpaces B S hS}
    (f : X ⟶ Y) (hf : IsLocallyOfFiniteType B S hS f.hom) (i : Y₀ ⟶ Y) (f₀ : X₀ ⟶ Y₀)
    (j : X₀ ⟶ X) (sq : IsPullback j.hom f₀.hom f.hom i.hom)
    (hi : ∀ W : Set (points B S hS Y.1), IsClosed W → W.Nonempty →
      ∃ y₀, pointsMap B S hS Y₀.1 i.hom y₀ ∈ W)
    {M N : Modules.{u, u} B S hS X.1 X.2} (hM : M.IsQuasicoherentOnSite)
    (hN : N.IsQuasicoherentOnSite) (hNft : SheafOfModules.IsFiniteTypeOnSite N)
    (hNprop : HasProperSupport B S hS X.2 Y.2 f.hom hf ((SheafOfModules.toSheaf _).obj N))
    (u : M ⟶ N) (hu : Epi ((modulePullback B S hS j).map u)) : Epi u := by
  set Q : Modules.{u, u} B S hS X.1 X.2 := cokernel u with hQ
  have hQqc : Q.IsQuasicoherentOnSite :=
    @isQuasicoherentOnSite_cokernel_unconditional B S hS X.1 X.2 M N hM hN u
  have hQft := isFiniteTypeOnSite_cokernel_of_isFiniteTypeOnSite B S hS X.1 X.2 u hNft
  have hZ := isClosed_supportOfSheaf_of_epi B S hS X.1 X.2 (cokernel.π u) hNft
  have hadj := modulePullbackAdjunction B S hS j
  have := hadj.isLeftAdjoint
  have : PreservesColimitsOfSize.{0, 0} (modulePullback B S hS j) :=
    hadj.leftAdjoint_preservesColimits
  have hQ0 : IsZero ((modulePullback B S hS j).obj Q) :=
    ((Preadditive.epi_iff_isZero_cokernel _).mp hu).of_iso
      (PreservesCokernel.iso (modulePullback B S hS j) u)
  have hpre : pointsMap B S hS X₀.1 j.hom ⁻¹'
      supportOfSheaf B S hS X.1 ((SheafOfModules.toSheaf _).obj Q) = ∅ := by
    rw [← supportOfSheaf_modulePullback_eq B S hS j Q hQqc hQft,
      supportOfSheaf_eq_empty_iff_isZero]
    exact hQ0
  have hQprop := hasProperSupport_of_subset B S hS X.2 Y.2 f.hom hf hZ
    (supportOfSheaf_cokernel_subset B S hS X u) hNprop
  obtain ⟨hQcl, hQproper⟩ := hQprop
  have hW := isClosed_image_of_isProperOver B S hS X.2 Y.2 Y.2 f.hom f.hom (𝟙 _)
    (Category.comp_id _) hf (isLocallyOfFiniteType_of_isLocallyOfFinitePresentation B S hS
      (isLocallyOfFinitePresentation_id B S hS Y.2))
    (isSeparated_of_isIso B S hS (𝟙 Y.1)) _ hQcl hQproper
  have hWempty : pointsMap B S hS X.1 f.hom ''
      supportOfSheaf B S hS X.1 ((SheafOfModules.toSheaf _).obj Q) = ∅ := by
    by_contra hne
    obtain ⟨y₀, x, hxZ, hx⟩ := hi _ hW (Set.nonempty_iff_ne_empty.2 hne)
    obtain ⟨w, hw, -⟩ := exists_points_of_isPullback B S hS sq x y₀ hx
    exact (Set.eq_empty_iff_forall_notMem.1 hpre w) (by rw [Set.mem_preimage, hw]; exact hxZ)
  rw [Preadditive.epi_iff_isZero_cokernel]
  exact (supportOfSheaf_eq_empty_iff_isZero B S hS X Q).mp (Set.image_eq_empty.1 hWempty)

end AlgebraicGeometry.Space
