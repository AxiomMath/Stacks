module

public import StacksFrontier.AlgebraicGeometry.Morphisms.FinitePresentationPoint
public import StacksFrontier.AlgebraicGeometry.Morphisms.Proper.ProperClosedSubset
public import StacksFrontier.AlgebraicGeometry.Morphisms.Support.Defs
public import StacksFrontier.AlgebraicGeometry.Perfect.ProperFlatGlobalSectionsUniversalModel
import StacksCore.Tactic.StacksAttribute

/-!
# One finite projective complex computing the cohomology of a finitely presented flat module

Let `R` be a ring, let `X` be a scheme of finite presentation over `R` and let `G` be a finitely
presented `𝒪_X`-module, flat over `R`, whose support is proper over `R`. Then there is a single
finite complex `M` of finite projective `R`-modules with

`RΓ(X_{R'}, G_{R'}) = M ⊗_R R'`

for every `R`-algebra `R'`.

Over the affine base `Spec R` the object `RΓ(X, G)` lives in `D(R)`, and it is isomorphic to a
bounded complex of finite projective `R`-modules exactly when it is pseudo-coherent and has finite
Tor dimension. Finite Tor dimension is proved here from flatness of `G` over `R`; pseudo-coherence
is taken as the hypothesis `PseudoCoherentDerivedGlobalSectionsOfProperSupport`.

## Main definitions

* `PseudoCoherentDerivedGlobalSectionsOfProperSupport`: the assertion that `RΓ(X, G)` is
  pseudo-coherent in `D(R)` for every scheme `X` of finite presentation over `R` and every finitely
  presented `𝒪_X`-module `G` flat over `R` with support proper over `R`.

## Main results

* `exists_finiteAffineCover_of_quasiCompact`: a quasi-compact separated morphism to an affine base
  admits a finite affine open cover whose finite intersections are affine.
* `hasFlatRepresentative_of_finitePresentation`: for such a morphism and a finitely presented `G`
  flat over `R`, the object `RΓ(X, G)` has a bounded termwise flat representative.
* `exists_finiteProjectiveModel_of_properSupport`: the finite projective model `M` together with,
  for every base change, the identification `RΓ(X_{R'}, G_{R'}) ≅ M ⊗_R R'`.

## Implementation notes

The morphism `f : X ⟶ Spec R` is assumed separated, in addition to being of finite presentation:
this makes the finite intersections of an affine open cover affine, so that the alternating Čech
complex computes `RΓ(X, G)`.

The identification for a base change is the inverse of the base-change map, followed by the model
and by the comparison of derived with ordinary extension of scalars, which is invertible because
the terms of `M` are projective, hence flat. Naturality in `R'` is not part of the statement.

Everything runs under `CategoryTheory.HasDerivedCategory.standard` at priority `10000`.

## References

* [Stacks Project, Tag 0A1I](https://stacks.math.columbia.edu/tag/0A1I)
* [Stacks Project, Tag 0A1H](https://stacks.math.columbia.edu/tag/0A1H)
* [Stacks Project, Tag 0CSC](https://stacks.math.columbia.edu/tag/0CSC)
* [Stacks Project, Tag 0DJQ](https://stacks.math.columbia.edu/tag/0DJQ)
* [Stacks Project, Tag 07VK](https://stacks.math.columbia.edu/tag/07VK)
* [Stacks Project, Tag 07VL](https://stacks.math.columbia.edu/tag/07VL)
* [Stacks Project, Tag 0657](https://stacks.math.columbia.edu/tag/0657)
* [Stacks Project, Tag 0658](https://stacks.math.columbia.edu/tag/0658)
* [Stacks Project, Tag 06XY](https://stacks.math.columbia.edu/tag/06XY)
* [Stacks Project, Tag 01U4](https://stacks.math.columbia.edu/tag/01U4)
* [Stacks Project, Tag 01XL](https://stacks.math.columbia.edu/tag/01XL)
* [Stacks Project, Tag 09RF](https://stacks.math.columbia.edu/tag/09RF)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
open Stacks.AlgebraicGeometry.ProperFlatGlobalSections

universe u

namespace Stacks.AlgebraicGeometry.FinitePresentationGlobalSectionsModel

attribute [local instance 10000] HasDerivedCategory.standard

/-! ### Pseudo-coherence over an arbitrary affine base -/

/-- For every ring `R`, scheme `X` of finite presentation over `R` and finitely presented
`𝒪_X`-module `G`, flat over `R`, whose support is proper over `R`, the object `RΓ(X, G)` of `D(R)`
is pseudo-coherent. -/
def PseudoCoherentDerivedGlobalSectionsOfProperSupport : Prop :=
  ∀ {R : Type u} [CommRing R] {X : Scheme.{u}} (f : X ⟶ Spec (.of R))
    (hf : FinitePresentation f) (G : X.Modules), G.IsFinitePresentation →
      IsFlatOver f.toLRSHom.toShHom G →
      (letI : LocallyOfFinitePresentation f := hf.locallyOfFinitePresentation
        ∃ Z : Closeds X, IsProperOver f Z ∧ SheafOfModules.supp G ⊆ (Z : Set X)) →
        StacksDraft.PseudoCoherence.IsPseudoCoherent (derivedGlobalSectionsOverBase f G)

/-! ### A finite affine cover with affine intersections -/

/-- **A quasi-compact separated morphism to an affine base admits a finite affine open cover whose
finite intersections are affine.** -/
theorem exists_finiteAffineCover_of_quasiCompact {R : Type u} [CommRing R]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of R)) [QuasiCompact f] [IsSeparated f] :
    ∃ (I : Type u) (_ : Fintype I) (_ : LinearOrder I) (U : I → X.Opens),
      (⊤ : X.Opens) = ⨆ i, U i ∧ (∀ i, IsAffineOpen (U i)) ∧
        ∀ (r : ℕ) (s : Fin (r + 1) → I), IsAffineOpen (⨅ k, U (s k)) := by
  classical
  have hcompact : CompactSpace ↥X := QuasiCompact.compactSpace_of_compactSpace f
  let C := X.affineOpenCover
  let V := C.openCover.finiteSubcover
  let T : X.AffineOpenCover.{u, u} :=
    { I₀ := V.I₀
      X i := C.X (C.openCover.idx i.1)
      f i := C.f (C.openCover.idx i.1)
      idx := V.idx
      covers := V.covers
      map_prop i := C.map_prop (C.openCover.idx i.1) }
  have hUaff : ∀ i, IsAffineOpen ((T.f i).opensRange) := fun i => isAffineOpen_opensRange (T.f i)
  exact ⟨T.I₀, inferInstance, linearOrderOfSTO WellOrderingRel, fun i => (T.f i).opensRange,
    T.openCover.iSup_opensRange.symm, hUaff,
    fun _ s => Stacks.Cech.inter_isAffineOpen f (fun i => (T.f i).opensRange) hUaff s⟩

/-! ### Finite Tor dimension -/

/-- **`RΓ(X, G)` has finite Tor dimension.** For a quasi-compact separated `f : X ⟶ Spec R` and a
finitely presented `𝒪_X`-module `G` flat over `R`, the object `RΓ(X, G)` of `D(R)` has a bounded
termwise flat representative. -/
theorem hasFlatRepresentative_of_finitePresentation {R : Type u} [CommRing R]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of R)) [QuasiCompact f] [IsSeparated f] (G : X.Modules)
    (hGfp : G.IsFinitePresentation) (hflat : IsFlatOver f.toLRSHom.toShHom G) :
    ∃ b : ℤ, StacksDraft.Perfect.HasFlatRepresentative.{u, u}
      (derivedGlobalSectionsOverBase f G) 0 b := by
  have := hGfp
  have : G.IsQuasicoherent := isQuasicoherent_of_isFinitePresentation G
  obtain ⟨I, hI, hIlin, U, hU, hUaff, haff⟩ := exists_finiteAffineCover_of_quasiCompact f
  exact ⟨(Fintype.card I : ℤ),
    hasFlatRepresentative_derivedGlobalSectionsOverBase f U hU G hUaff haff hflat⟩

/-! ### The finite projective model -/

/-- Let `R` be a ring, let `X` be a scheme of finite presentation over `R`, separated over `R`,
and let `G` be a finitely presented `𝒪_X`-module, flat over `R`, whose support is proper over `R`.
Assume `hres`, pseudo-coherence of `RΓ(X, G)` in this generality. Then there is a finite complex
`M` of finite projective `R`-modules such that for every homomorphism `φ : R ⟶ R'` and every
cartesian square exhibiting `X'` as the base change of `X` along `Spec R' ⟶ Spec R`,

`RΓ(X_{R'}, G_{R'}) ≅ M ⊗_R R'`  in  `D(R')`.

Naturality of this identification in `R'` is not asserted. -/
@[stacks 0A1I "existence of the finite projective model M and the identification \
RGamma(X_{R'}, G_{R'}) = M tensor_R R' for every base change; naturality in R' NOT stated. \
CARRIED: the pseudo-coherence half of the perfection, as the named residue \
PseudoCoherentDerivedGlobalSectionsOfProperSupport, and separatedness of f, a narrowing. \
Proved: the finite-Tor-dimension half and the identification. Accounting in the docstring"]
theorem exists_finiteProjectiveModel_of_properSupport
    (hres : PseudoCoherentDerivedGlobalSectionsOfProperSupport.{u})
    {R : Type u} [CommRing R] {X : Scheme.{u}} (f : X ⟶ Spec (.of R)) [IsSeparated f]
    (hf : FinitePresentation f) (G : X.Modules) (hGfp : G.IsFinitePresentation)
    (hflat : IsFlatOver f.toLRSHom.toShHom G)
    (hsupp : letI : LocallyOfFinitePresentation f := hf.locallyOfFinitePresentation
      ∃ Z : Closeds X, IsProperOver f Z ∧ SheafOfModules.supp G ⊆ (Z : Set X)) :
    ∃ (M : CochainComplex (ModuleCat.{u} R) ℤ) (a b : ℤ),
      M.IsStrictlyGE a ∧ M.IsStrictlyLE b ∧
        (∀ i : ℤ, Module.Finite R (M.X i)) ∧ (∀ i : ℤ, Module.Projective R (M.X i)) ∧
        ∀ {R' : Type u} [CommRing R'] (φ : R →+* R') {X' : Scheme.{u}}
          {f' : X' ⟶ Spec (.of R')} {g : X' ⟶ X}
          (_hsq : IsPullback g f' f (Spec.map (CommRingCat.ofHom φ))),
          Nonempty (derivedGlobalSectionsOverBase f' ((Scheme.Modules.pullback g).obj G) ≅
            DerivedCategory.Q.obj (extendScalarsComplex φ M)) := by
  have := hGfp
  have : G.IsQuasicoherent := isQuasicoherent_of_isFinitePresentation G
  have : QuasiCompact f := hf.quasiCompact
  obtain ⟨I, hI, hIlin, U, hU, hUaff, haff⟩ := exists_finiteAffineCover_of_quasiCompact f
  obtain ⟨c, hc⟩ := hasFlatRepresentative_of_finitePresentation f G hGfp hflat
  obtain ⟨M, a, b, hGE, hLE, hfin, hproj, ⟨e⟩⟩ :=
    (StacksDraft.Perfect.isPerfect_iff_pseudoCoherent_and_finiteTorDimension.{u, u}
        (derivedGlobalSectionsOverBase f G)).1.mpr
      ⟨hres f hf G hGfp hflat hsupp, 0, c, hc⟩
  refine ⟨M, a, b, hGE, hLE, hfin, hproj, ?_⟩
  intro R' _ φ X' f' g hsq
  have (n : ℤ) : Module.Flat R (M.X n) :=
    have := hproj n
    Module.Flat.of_projective
  have := isIso_derivedGlobalSectionsBaseChangeMap φ hsq G U hU hUaff haff hflat
  exact ⟨(asIso (derivedGlobalSectionsBaseChangeMap φ hsq G U hU hUaff haff)).symm ≪≫
    (StacksDraft.PseudoCoherence.extendScalarsDerived φ).mapIso e ≪≫
    StacksDraft.PseudoCoherence.extendScalarsDerivedIsoOfFlat φ M b⟩

end Stacks.AlgebraicGeometry.FinitePresentationGlobalSectionsModel

end
