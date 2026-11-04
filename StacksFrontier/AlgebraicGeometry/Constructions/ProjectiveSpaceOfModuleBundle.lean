module

public import StacksFrontier.AlgebraicGeometry.Constructions.ProjectiveSpaceOfModule
public import StacksFrontier.AlgebraicGeometry.SymSectionsBaseChange.SectionRing
public import StacksFrontier.AlgebraicGeometry.FiniteMorphismProjective.AffineBase
public import StacksFrontier.AlgebraicGeometry.Morphisms.Projective.BaseChange
public import StacksFrontier.AlgebraicGeometry.Blowup.ProjRegrading
public import StacksFrontier.AlgebraicGeometry.Blowup.RelativeProj
public import StacksFrontier.AlgebraicGeometry.SymAlgebraQcohPieces.Basic
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SymmetricPowerSheafification
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The projective space of a module is the projective bundle of its associated sheaf

Let `V` be a module over a commutative ring `k`. Its projective space is
`𝐏(V) = Proj(Sym_k V)` (Tag 0FCY), and reading `V` as the quasi-coherent `𝒪_{Spec k}`-module
`V~` it also has a projective bundle `𝐏(V~) = Proj_{Spec k}(Sym(V~))` (Tag 01OB). This file
identifies the two **as schemes over `Spec k`**, which is the assertion of Tag 0FCY that the
projective space of a vector space is the projective space bundle of the corresponding
quasi-coherent module on the spectrum of the base field.

## Main definitions

* `AlgebraicGeometry.tildeOfModule`: the quasi-coherent `𝒪_{Spec k}`-module `V~`.
* `AlgebraicGeometry.topGradedHom` and `AlgebraicGeometry.topGradedInv`: **mutually inverse
  homomorphisms of graded rings between the graded ring of global sections of `Sym(V~)` and
  `Sym_k V`.**
* `AlgebraicGeometry.projectiveSpaceOfModuleIsoSchemeProjectiveBundle`: `𝐏(V)` is the projective
  bundle of `V~` in the presentation `Stacks.SymGraded.schemeProjectiveBundle`.

## Main results

* `AlgebraicGeometry.specMap_gradedZeroRingHom_comp`: **the degree-zero half** of the graded
  identification: the structure map of the graded ring of global sections, corestricted to
  degree zero, becomes `k ⟶ Sym⁰_k V` once the global functions on `Spec k` are identified with
  `k` and the spectrum of the ring of global functions with `Spec k`.
* `AlgebraicGeometry.projectiveSpaceOfModuleIsoSchemeProjectiveBundle_hom_comp_toBase`: that
  identification is one over `Spec k`.
* `AlgebraicGeometry.exists_iso_projectiveBundle_tildeOfModule`: **Tag 0FCY, the projective
  bundle clause.** `𝐏(V)` is isomorphic to `Stacks.RelativeProj.projectiveBundle (Spec k) V~` by
  an isomorphism carrying the structure morphism of `𝐏(V)` to the projection of the bundle.

## Implementation notes

**The route is through the graded ring of sections over the whole of `Spec k`.** The lemma the
exercise turns on is `Stacks.SymGraded.AffinePieces.symSectionRingEquiv`: over an affine open the
graded ring of sections of `Sym(ℰ)` is the symmetric algebra of the sections of `ℰ`, as graded
rings, and by `Stacks.SymGraded.AffinePieces.symSectionAlgEquiv` as algebras over the functions
on that open. At the top open of `Spec k` this reads the graded ring of global sections of
`Sym(V~)` as `Sym_{Γ(Spec k, ⊤)}(Γ(V~, ⊤))`, and the remaining step is the transport along
`AlgebraicGeometry.Scheme.ΓSpecIso` and the unit `AlgebraicGeometry.tilde.toOpen` at the top
open, both of which are isomorphisms. That transport is *semilinear*: the ring and the module
change together, so it is `SymmetricAlgebra.mapₛₗ`, whose inverse is `mapₛₗ` of the inverse data
and whose round trips are `SymmetricAlgebra.mapₛₗ_eq_comp` and `mapₛₗ_eq_self`.

**It does not go through `Stacks.SymGraded.projectiveBundleIsoProjectiveSpaceOfModule`**, the
comparison of `StacksFrontier.AlgebraicGeometry.SheafSymmetricAlgebra.ProjComparison`, and
the reason is the presentation. That comparison is for `Stacks.SymGraded.symSheafGradedAlgebra`,
built from the associated sheaf of the *global sections* of the symmetric algebra, whereas the
projective bundle of Tag 01OB is built from `Stacks.SymGraded.schemeSheafGradedAlgebra`, the
degreewise *sheafification* of the sectionwise symmetric algebra. Nothing relates the two as
graded algebras: as the implementation notes of
`StacksFrontier.AlgebraicGeometry.SymAlgebraQcohPieces.Basic` record, nothing is proved about the
multiplication or the unit of `Stacks.SymGraded.schemeSymAlgebra` under restriction, so the
available comparison is piecewise and is not a morphism of graded algebras. It is also an
isomorphism of bare schemes only, which is not what this clause asserts.

**Over the affine base the relative homogeneous spectrum is the chart at the top open**, which is
`Stacks.FiniteMorphismProjective.projTopIso`, with its structure-morphism companion
`Stacks.FiniteMorphismProjective.projTopIso_hom_toBase`; the passage from that presentation to
`Stacks.RelativeProj.projectiveBundle` is `AlgebraicGeometry.projectiveBundlePresentationsAgree`.
Both are compatible with the projections to the base, which is what makes the statement an
isomorphism over `Spec k` rather than of bare schemes.

**Why several spellings of one object are named.** `AlgebraicGeometry.specTopSite` and
`AlgebraicGeometry.strZeroTop` exist only to fix a spelling. The grading of the graded ring of
sections appears both as `A.grading ⊤`, which is what
`Stacks.FiniteMorphismProjective.projTopIso` and `AlgebraicGeometry.Proj.map_toSpecZero` use, and
as the field `grading` of the bridged
`Stacks.AlgebraicGeometry.RelativeProj.GradedAlgebra` at the top open, which is what
`Stacks.AlgebraicGeometry.RelativeProj.GradedAlgebra.toBase` unfolds to. The two are
definitionally equal but neither instance search nor `rw`'s type-correctness check sees through
the unfolding, so the terms that must be rewritten are given names carrying the first spelling.

## References

* [Stacks Project, Tag 0FCY](https://stacks.math.columbia.edu/tag/0FCY)
* [Stacks Project, Tag 01OB](https://stacks.math.columbia.edu/tag/01OB)
* [Stacks Project, Tag 01NN](https://stacks.math.columbia.edu/tag/01NN)
* [Stacks Project, Tag 01NQ](https://stacks.math.columbia.edu/tag/01NQ)

## On the numbering

Tag 0FCY is an `\begin{example}` of unnumbered prose and **has no numbered clauses at all**. The
labels "clause (1)" … "clause (6)" used in this file and in
`StacksFrontier.AlgebraicGeometry.Constructions.ProjectiveSpaceGeneratingSections` and
`…ProjectiveSpaceCoordinateSquare` are this library's own labelling of its six assertions:
(1) `𝐏(V) = Proj(Sym_k V)`; (2) `𝐏(V) ≅ ℙⁿ_k` when `dim V = n + 1`; (3) `𝐏(V)` is the projective
bundle of `V~` over `Spec k`; (4) a `k`-valued point of `𝐏(V)` is a surjection `V → L_p` with
`dim L_p = 1`; (5) the morphism `φ_{ℒ,ψ}` attached to generating sections, over `k`, with its
twist isomorphism `θ` and the recovery of `ψ`; (6) the coordinate square against
[Stacks, Tag 01ND]. **None of these numbers occur in the source.**

## Not done here

Nothing of Tag 0FCY. Its clause (4) and its two twist clauses are proved elsewhere:

* What the tag asserts in clause (4) is the correspondence between `k`-valued points of `𝐏(V)`
  and one-dimensional quotients of `V`, and that is **proved**, as a bijection:
  `AlgebraicGeometry.ProjectiveSpaceOfModule.kValuedPointEquivOneDimQuotient`
  (`Constructions/ProjectiveSpaceOfModulePoints.lean`), with
  `mem_kValuedPointEquivOneDimQuotient` identifying it.
* The representability of the functor of `𝒪_T`-module quotients of `f^*ℰ` that are locally free
  of rank one belongs to the **unlabelled discussion of Section 01OB that precedes the example**,
  not to Tag 0FCY, and so is not a clause of this tag at all.
* The twist isomorphism the tag does ask for, `θ : φ_{ℒ,ψ}^*𝒪_{𝐏(V)}(1) ≅ ℒ` together with the
  agreement of `ψ` with the composition through `Γ(𝐏(V), 𝒪(1))`, is **proved**:
  `Stacks.AlgebraicGeometry.ProjectiveSpaceGeneratingSections.twistIsoOfGeneratingSections` and
  `twistIso_pullbackSectionOne`.

What is genuinely absent is a comparison of `𝒪(n)` *along the projective-bundle identification
of this file*, which no clause of the tag asks for; it would need the third assertion of
Tag 01MZ.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry
open Stacks.AlgebraicGeometry.RelativeProjBridge
open Stacks.AlgebraicGeometry.RelativeProj
open Stacks.SymGraded Stacks.SymGraded.AffinePieces

namespace AlgebraicGeometry

universe u

variable (k V : Type u) [CommRing k] [AddCommGroup V] [Module k V]

/-! ### The associated sheaf of a module on the spectrum of its base ring -/

/-- The quasi-coherent `𝒪_{Spec k}`-module associated to a `k`-module `V`. -/
abbrev tildeOfModule : (Spec (CommRingCat.of k)).Modules :=
  tilde (R := CommRingCat.of k) (ModuleCat.of k V)

/-- Every homogeneous piece of the symmetric algebra of the associated sheaf of a module is
quasi-coherent, the associated sheaf being so. -/
abbrev tildeIsQuasicoherentPieces : IsQuasicoherentPieces (tildeOfModule k V) :=
  isQuasicoherentPieces_of_isQuasicoherent _

/-- The whole of `Spec k`, as an object of its small affine Zariski site. Named, rather than
written as an anonymous pair, because `AlgebraicGeometry.Scheme.AffineZariskiSite` is a
definition and a pair elaborated at the underlying subtype is not recognised as living in it
without unfolding it. -/
def specTopSite : (Spec (CommRingCat.of k)).AffineZariskiSite :=
  ⟨⊤, isAffineOpen_top (Spec (CommRingCat.of k))⟩

/-- The identification of `k` with the global functions on `Spec k`. -/
abbrev specΓInv : k →+* ↥Γ(Spec (CommRingCat.of k), ⊤) :=
  (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom

/-- The identification of the global functions on `Spec k` with `k`. -/
abbrev specΓHom : ↥Γ(Spec (CommRingCat.of k), ⊤) →+* k :=
  (Scheme.ΓSpecIso (CommRingCat.of k)).hom.hom

/-- The two identifications of `k` with the global functions on `Spec k` are mutually inverse. -/
theorem specΓHom_specΓInv (r : k) : specΓHom k (specΓInv k r) = r := by
  show ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫
    (Scheme.ΓSpecIso (CommRingCat.of k)).hom).hom r = r
  rw [Iso.inv_hom_id]
  rfl

/-- The two identifications of `k` with the global functions on `Spec k` are mutually inverse. -/
theorem specΓInv_specΓHom (r : ↥Γ(Spec (CommRingCat.of k), ⊤)) :
    specΓInv k (specΓHom k r) = r := by
  show ((Scheme.ΓSpecIso (CommRingCat.of k)).hom ≫
    (Scheme.ΓSpecIso (CommRingCat.of k)).inv).hom r = r
  rw [Iso.hom_inv_id]
  rfl

/-- Restriction from the top open to itself is the identity on global functions. This is what
makes the `k`-action on the global sections of a module on `Spec k` the action of the global
functions through `AlgebraicGeometry.Scheme.ΓSpecIso`. -/
theorem presheaf_map_leTop_top (y : ↥Γ(Spec (CommRingCat.of k), ⊤)) :
    (Spec (CommRingCat.of k)).presheaf.map
      (TopologicalSpace.Opens.leTop (⊤ : (Spec (CommRingCat.of k)).Opens)).op y = y := by
  have h : (TopologicalSpace.Opens.leTop (⊤ : (Spec (CommRingCat.of k)).Opens)).op =
      𝟙 (Opposite.op (⊤ : (Spec (CommRingCat.of k)).Opens)) := rfl
  rw [h, CategoryTheory.Functor.map_id]
  rfl

/-- Scaling a global section of `V~` by an element of `k` is scaling it by the corresponding
global function on `Spec k`, restricted to the top open. -/
theorem specΓInv_smul_top (c : k) (y : ↥Γ(tildeOfModule k V, ⊤)) :
    specΓInv k c • y =
      (Spec (CommRingCat.of k)).presheaf.map
        (TopologicalSpace.Opens.leTop (⊤ : (Spec (CommRingCat.of k)).Opens)).op
        (specΓInv k c) • y := by
  rw [presheaf_map_leTop_top]

/-- **The unit of the associated sheaf at the top open, as a semilinear map.** The canonical map
`V ⟶ Γ(Spec k, V~)` is linear over `k` acting on the target through
`AlgebraicGeometry.Scheme.ΓSpecIso`. -/
def tildeToOpenTopₛₗ : V →ₛₗ[specΓInv k] ↥Γ(tildeOfModule k V, ⊤) where
  toFun := (tilde.toOpen (R := CommRingCat.of k) (ModuleCat.of k V) ⊤).hom
  map_add' x y := map_add _ x y
  map_smul' c x :=
    Eq.trans (map_smul (tilde.toOpen (R := CommRingCat.of k) (ModuleCat.of k V) ⊤).hom c x)
      (specΓInv_smul_top k V c
        ((tilde.toOpen (R := CommRingCat.of k) (ModuleCat.of k V) ⊤).hom x)).symm

/-- The semilinear unit is the unit of Mathlib's associated sheaf. -/
@[simp]
theorem tildeToOpenTopₛₗ_apply (x : V) :
    tildeToOpenTopₛₗ k V x =
      (tilde.toOpen (R := CommRingCat.of k) (ModuleCat.of k V) ⊤).hom x := rfl

/-- The inverse of the unit at the top open, as a function. The unit is an isomorphism by
Mathlib's `AlgebraicGeometry.tilde.isIso_toOpen_top`. -/
def tildeFromOpenTop : ↥Γ(tildeOfModule k V, ⊤) → V :=
  (tilde.isoTop (R := CommRingCat.of k) (ModuleCat.of k V)).inv.hom

/-- The inverse of the unit is a right inverse. -/
theorem tildeToOpenTop_fromOpenTop (y : ↥Γ(tildeOfModule k V, ⊤)) :
    tildeToOpenTopₛₗ k V (tildeFromOpenTop k V y) = y :=
  DFunLike.congr_fun (congrArg ModuleCat.Hom.hom
    (tilde.isoTop (R := CommRingCat.of k) (ModuleCat.of k V)).inv_hom_id) y

/-- The inverse of the unit is a left inverse. -/
theorem tildeFromOpenTop_toOpenTop (x : V) :
    tildeFromOpenTop k V (tildeToOpenTopₛₗ k V x) = x :=
  DFunLike.congr_fun (congrArg ModuleCat.Hom.hom
    (tilde.isoTop (R := CommRingCat.of k) (ModuleCat.of k V)).hom_inv_id) x

/-- The unit at the top open is injective, having a left inverse. -/
theorem tildeToOpenTopₛₗ_injective : Function.Injective (tildeToOpenTopₛₗ k V) := fun x y h => by
  rw [← tildeFromOpenTop_toOpenTop k V x, ← tildeFromOpenTop_toOpenTop k V y, h]

/-- **The inverse of the unit at the top open, as a semilinear map**, along the identification of
the global functions on `Spec k` with `k`. -/
def tildeFromOpenTopₛₗ : ↥Γ(tildeOfModule k V, ⊤) →ₛₗ[specΓHom k] V where
  toFun := tildeFromOpenTop k V
  map_add' x y := map_add
    (tilde.isoTop (R := CommRingCat.of k) (ModuleCat.of k V)).inv.hom x y
  map_smul' s y := by
    refine tildeToOpenTopₛₗ_injective k V ?_
    rw [tildeToOpenTop_fromOpenTop, map_smulₛₗ, tildeToOpenTop_fromOpenTop,
      specΓInv_specΓHom]

/-- The semilinear inverse of the unit is the inverse of the unit. -/
@[simp]
theorem tildeFromOpenTopₛₗ_apply (y : ↥Γ(tildeOfModule k V, ⊤)) :
    tildeFromOpenTopₛₗ k V y = tildeFromOpenTop k V y := rfl

/-! ### The symmetric algebra of the global sections -/

/-- **The symmetric algebra of the global sections of `V~` over the global functions on `Spec k`
is the symmetric algebra of `V` over `k`**, the forward map. -/
def symSectionsTopHom :
    SymmetricAlgebra ↥Γ(Spec (CommRingCat.of k), ⊤) ↥Γ(tildeOfModule k V, ⊤) →+*
      SymmetricAlgebra k V :=
  SymmetricAlgebra.mapₛₗ (specΓHom k) (tildeFromOpenTopₛₗ k V)

/-- The backward map of `AlgebraicGeometry.symSectionsTopHom`. -/
def symSectionsTopInv :
    SymmetricAlgebra k V →+*
      SymmetricAlgebra ↥Γ(Spec (CommRingCat.of k), ⊤) ↥Γ(tildeOfModule k V, ⊤) :=
  SymmetricAlgebra.mapₛₗ (specΓInv k) (tildeToOpenTopₛₗ k V)

/-- Base change along mutually inverse semilinear maps is a left inverse on symmetric algebras. -/
private theorem mapₛₗ_mapₛₗ_of_inverse {R S M N : Type*} [CommRing R] [CommRing S]
    [AddCommGroup M] [AddCommGroup N] [Module R M] [Module S N] {φ : R →+* S} {ψ : S →+* R}
    (u : M →ₛₗ[φ] N) (w : N →ₛₗ[ψ] M) (hφ : ∀ r, ψ (φ r) = r) (hu : ∀ m, w (u m) = m)
    (x : SymmetricAlgebra R M) :
    SymmetricAlgebra.mapₛₗ ψ w (SymmetricAlgebra.mapₛₗ φ u x) = x :=
  (SymmetricAlgebra.mapₛₗ_eq_comp u w LinearMap.id (fun r => (hφ r).symm)
    (fun m => (hu m).symm) x).symm.trans
      (SymmetricAlgebra.mapₛₗ_eq_self LinearMap.id (fun _ => rfl) (fun _ => rfl) x)

/-- The two transports of the symmetric algebra are mutually inverse. -/
theorem symSectionsTopHom_inv (x : SymmetricAlgebra k V) :
    symSectionsTopHom k V (symSectionsTopInv k V x) = x :=
  mapₛₗ_mapₛₗ_of_inverse _ _ (specΓHom_specΓInv k) (tildeFromOpenTop_toOpenTop k V) x

/-- The two transports of the symmetric algebra are mutually inverse. -/
theorem symSectionsTopInv_hom
    (x : SymmetricAlgebra ↥Γ(Spec (CommRingCat.of k), ⊤) ↥Γ(tildeOfModule k V, ⊤)) :
    symSectionsTopInv k V (symSectionsTopHom k V x) = x :=
  mapₛₗ_mapₛₗ_of_inverse _ _ (specΓInv_specΓHom k) (tildeToOpenTop_fromOpenTop k V) x

/-- The transport carries the structure map of the symmetric algebra of the global sections to
the structure map of `Sym_k V`, along the identification of the global functions with `k`. -/
theorem symSectionsTopHom_algebraMap (r : ↥Γ(Spec (CommRingCat.of k), ⊤)) :
    symSectionsTopHom k V
        (algebraMap ↥Γ(Spec (CommRingCat.of k), ⊤)
          (SymmetricAlgebra ↥Γ(Spec (CommRingCat.of k), ⊤) ↥Γ(tildeOfModule k V, ⊤)) r) =
      algebraMap k (SymmetricAlgebra k V) (specΓHom k r) :=
  SymmetricAlgebra.mapₛₗ_algebraMap (specΓHom k) (tildeFromOpenTopₛₗ k V) r

/-! ### The graded identification at the top open -/

/-- The graded ring of sections of `Sym(V~)` over the whole of `Spec k`, read as the symmetric
algebra of `V` over `k`. -/
def topSectionRingEquiv :
    (schemeSheafGradedAlgebra (tildeOfModule k V) (tildeIsQuasicoherentPieces k V)).sectionRing ⊤
      ≃+* SymmetricAlgebra k V :=
  (symSectionRingEquiv (tildeOfModule k V) (isAffineOpen_top (Spec (CommRingCat.of k)))
    (tildeIsQuasicoherentPieces k V)).trans
    (RingEquiv.ofRingHom (symSectionsTopHom k V) (symSectionsTopInv k V)
      (RingHom.ext (symSectionsTopHom_inv k V)) (RingHom.ext (symSectionsTopInv_hom k V)))

/-- The identification at the top open, unfolded: the identification of the graded ring of
sections with the symmetric algebra of the sections, followed by the transport to `k` and `V`. -/
@[simp]
theorem topSectionRingEquiv_apply
    (x : (schemeSheafGradedAlgebra (tildeOfModule k V)
      (tildeIsQuasicoherentPieces k V)).sectionRing ⊤) :
    topSectionRingEquiv k V x =
      symSectionsTopHom k V (symSectionRingEquiv (tildeOfModule k V)
        (isAffineOpen_top (Spec (CommRingCat.of k))) (tildeIsQuasicoherentPieces k V) x) := rfl

/-- **The graded identification at the top open**: the graded ring of global sections of
`Sym(V~)` is `Sym_k V`, as a graded ring. -/
def topGradedHom :
    (schemeSheafGradedAlgebra (tildeOfModule k V)
        (tildeIsQuasicoherentPieces k V)).grading ⊤ →+*ᵍ
      (fun n : ℕ => SymPow.symmetricPower n k V) where
  toRingHom := (topSectionRingEquiv k V).toRingHom
  map_mem {i _} hx :=
    SymmetricAlgebra.mapₛₗ_mem_symmetricPower (specΓHom k) (tildeFromOpenTopₛₗ k V) i
      ((mem_symmetricPower_symSectionRingEquiv (tildeOfModule k V)
        (isAffineOpen_top (Spec (CommRingCat.of k))) (tildeIsQuasicoherentPieces k V) i _).2 hx)

/-- The inverse of the identification at the top open, read before the transport. -/
theorem symSectionRingEquiv_topSectionRingEquiv_symm (x : SymmetricAlgebra k V) :
    symSectionRingEquiv (tildeOfModule k V) (isAffineOpen_top (Spec (CommRingCat.of k)))
        (tildeIsQuasicoherentPieces k V) ((topSectionRingEquiv k V).symm x) =
      symSectionsTopInv k V x :=
  (symSectionsTopInv_hom k V _).symm.trans (congrArg (symSectionsTopInv k V)
    ((topSectionRingEquiv k V).apply_symm_apply x))

/-- The inverse of the identification at the top open respects the grading. -/
theorem topSectionRingEquiv_symm_mem_grading (i : ℕ) {x : SymmetricAlgebra k V}
    (hx : x ∈ SymPow.symmetricPower i k V) :
    (topSectionRingEquiv k V).symm x ∈
      (schemeSheafGradedAlgebra (tildeOfModule k V)
        (tildeIsQuasicoherentPieces k V)).grading ⊤ i := by
  refine (mem_symmetricPower_symSectionRingEquiv (tildeOfModule k V)
    (isAffineOpen_top (Spec (CommRingCat.of k))) (tildeIsQuasicoherentPieces k V) i _).1 ?_
  rw [symSectionRingEquiv_topSectionRingEquiv_symm]
  exact SymmetricAlgebra.mapₛₗ_mem_symmetricPower (specΓInv k) (tildeToOpenTopₛₗ k V) i hx

/-- The inverse of `AlgebraicGeometry.topGradedHom`. -/
def topGradedInv :
    (fun n : ℕ => SymPow.symmetricPower n k V) →+*ᵍ
      (schemeSheafGradedAlgebra (tildeOfModule k V)
        (tildeIsQuasicoherentPieces k V)).grading ⊤ where
  toRingHom := (topSectionRingEquiv k V).symm.toRingHom
  map_mem {i _} hx := topSectionRingEquiv_symm_mem_grading k V i hx

/-- `AlgebraicGeometry.topGradedInv` is a right inverse of `AlgebraicGeometry.topGradedHom`. -/
theorem topGradedHom_comp_inv :
    (topGradedHom k V).comp (topGradedInv k V) =
      GradedRingHom.id (fun n : ℕ => SymPow.symmetricPower n k V) :=
  GradedRingHom.ext fun x => (topSectionRingEquiv k V).apply_symm_apply x

/-- `AlgebraicGeometry.topGradedInv` is a left inverse of `AlgebraicGeometry.topGradedHom`. -/
theorem topGradedInv_comp_hom :
    (topGradedInv k V).comp (topGradedHom k V) =
      GradedRingHom.id ((schemeSheafGradedAlgebra (tildeOfModule k V)
        (tildeIsQuasicoherentPieces k V)).grading ⊤) :=
  GradedRingHom.ext fun x => (topSectionRingEquiv k V).symm_apply_apply x

/-! ### The degree-zero half of the identification -/

/-- The identification carries the structure map of the graded ring of global sections to the
structure map of the symmetric algebra. -/
theorem symSectionRingEquiv_strHom (r : ↥Γ(Spec (CommRingCat.of k), ⊤)) :
    symSectionRingEquiv (tildeOfModule k V) (isAffineOpen_top (Spec (CommRingCat.of k)))
        (tildeIsQuasicoherentPieces k V)
        ((schemeSheafGradedAlgebra (tildeOfModule k V)
          (tildeIsQuasicoherentPieces k V)).strHom ⊤ r) =
      algebraMap ↥Γ(Spec (CommRingCat.of k), ⊤)
        (SymmetricAlgebra ↥Γ(Spec (CommRingCat.of k), ⊤) ↥Γ(tildeOfModule k V, ⊤)) r := by
  let _ := sectionAlgebra (tildeOfModule k V) (tildeIsQuasicoherentPieces k V)
    (V := (⊤ : (Spec (CommRingCat.of k)).Opens))
  rw [← algebraMap_sectionRingAlgebra (schemeSheafGradedAlgebra (tildeOfModule k V)
    (tildeIsQuasicoherentPieces k V)) ⊤ r]
  exact (symSectionAlgEquiv (tildeOfModule k V) (isAffineOpen_top (Spec (CommRingCat.of k)))
    (tildeIsQuasicoherentPieces k V)).commutes r

/-- The structure map of the graded ring of global sections of `Sym(V~)`, corestricted to
degree zero. Named so that its target is spelled by the grading of the graded ring of sections
over the top open, which is the spelling `AlgebraicGeometry.Proj.map_toSpecZero` produces for
`AlgebraicGeometry.topGradedHom`. -/
def strZeroTop :
    Γ(Spec (CommRingCat.of k), ⊤) ⟶
      CommRingCat.of ↥((schemeSheafGradedAlgebra (tildeOfModule k V)
        (tildeIsQuasicoherentPieces k V)).grading ⊤ 0) :=
  (schemeSheafGradedAlgebra (tildeOfModule k V)
    (tildeIsQuasicoherentPieces k V)).toGradedAlgebra.strZero (specTopSite k)

/-- **The degree-zero half of the graded identification at the top open**, on elements. -/
theorem coe_gradedZeroRingHom_strZeroTop (r : ↥Γ(Spec (CommRingCat.of k), ⊤)) :
    ((topGradedHom k V).gradedZeroRingHom (strZeroTop k V r) : SymmetricAlgebra k V) =
      algebraMap k (SymmetricAlgebra k V) (specΓHom k r) := by
  refine Eq.trans ?_ ((congrArg (symSectionsTopHom k V)
    (symSectionRingEquiv_strHom k V r)).trans (symSectionsTopHom_algebraMap k V r))
  exact congrArg (fun z : (schemeSheafGradedAlgebra (tildeOfModule k V)
      (tildeIsQuasicoherentPieces k V)).sectionRing ⊤ =>
    symSectionsTopHom k V (symSectionRingEquiv (tildeOfModule k V)
      (isAffineOpen_top (Spec (CommRingCat.of k))) (tildeIsQuasicoherentPieces k V) z))
    (GradedAlgebra.coe_strZero_apply (schemeSheafGradedAlgebra (tildeOfModule k V)
      (tildeIsQuasicoherentPieces k V)).toGradedAlgebra (specTopSite k) r)

/-- **The degree-zero half of the graded identification at the top open.** The structure map of
the graded ring of global sections of `Sym(V~)`, corestricted to degree zero, becomes the
structure map `k ⟶ Sym⁰_k V` of the projective space of `V` once the global functions on
`Spec k` are identified with `k` and the spectrum of the ring of global functions with
`Spec k`. -/
theorem specMap_gradedZeroRingHom_comp :
    Spec.map (CommRingCat.ofHom (topGradedHom k V).gradedZeroRingHom) ≫
          Spec.map (strZeroTop k V) ≫
          Spec.map (Scheme.ΓSpecIso (CommRingCat.of k)).inv =
      Spec.map (CommRingCat.ofHom (algebraMap k ↥(SymPow.symmetricPower 0 k V))) := by
  rw [← Spec.map_comp, ← Spec.map_comp]
  refine congrArg Spec.map (CommRingCat.hom_ext (RingHom.ext fun r => Subtype.ext ?_))
  refine Eq.trans (coe_gradedZeroRingHom_strZeroTop k V (specΓInv k r)) ?_
  rw [specΓHom_specΓInv]
  rfl

/-! ### The projective space of a module is the projective bundle of its associated sheaf -/

/-- The irrelevant ideal of `Sym_k V` is covered by that of the graded ring of global sections of
`Sym(V~)`, so the identification of the two induces a morphism of projective spectra. -/
theorem irrelevant_le_map_topGradedHom :
    HomogeneousIdeal.irrelevant (fun n : ℕ => SymPow.symmetricPower n k V) ≤
      (HomogeneousIdeal.irrelevant ((schemeSheafGradedAlgebra (tildeOfModule k V)
        (tildeIsQuasicoherentPieces k V)).grading ⊤)).map (topGradedHom k V) :=
  Stacks.GradedRegrading.irrelevant_le_map_of_comp_eq_id (topGradedHom_comp_inv k V)

/-- The irrelevant ideal of the graded ring of global sections of `Sym(V~)` is covered by that of
`Sym_k V`. -/
theorem irrelevant_le_map_topGradedInv :
    HomogeneousIdeal.irrelevant ((schemeSheafGradedAlgebra (tildeOfModule k V)
        (tildeIsQuasicoherentPieces k V)).grading ⊤) ≤
      (HomogeneousIdeal.irrelevant (fun n : ℕ => SymPow.symmetricPower n k V)).map
        (topGradedInv k V) :=
  Stacks.GradedRegrading.irrelevant_le_map_of_comp_eq_id (topGradedInv_comp_hom k V)

/-- **The projective space of `V` is `Proj` of the graded ring of global sections of
`Sym(V~)`**, by the graded identification of the two. -/
def projectiveSpaceOfModuleIsoProjTop :
    projectiveSpaceOfModule k V ≅
      Proj ((schemeSheafGradedAlgebra (tildeOfModule k V)
        (tildeIsQuasicoherentPieces k V)).grading ⊤) :=
  haveI : IsIso (Proj.map (topGradedHom k V) (irrelevant_le_map_topGradedHom k V)) :=
    Proj.isIso_map (irrelevant_le_map_topGradedHom k V) (irrelevant_le_map_topGradedInv k V)
      (topGradedInv_comp_hom k V) (topGradedHom_comp_inv k V)
  asIso (Proj.map (topGradedHom k V) (irrelevant_le_map_topGradedHom k V))

/-- The forward morphism of `projectiveSpaceOfModuleIsoProjTop` is the morphism of projective
spectra induced by `topGradedHom`. -/
@[simp]
theorem projectiveSpaceOfModuleIsoProjTop_hom :
    (projectiveSpaceOfModuleIsoProjTop k V).hom =
      Proj.map (topGradedHom k V) (irrelevant_le_map_topGradedHom k V) := rfl

/-- The structure morphism of the chart of the relative homogeneous spectrum over the whole of
`Spec k`, with the identification of `Spec k` with the spectrum of its ring of global functions
carried out. -/
theorem toBase_top_eq :
    (schemeSheafGradedAlgebra (tildeOfModule k V)
        (tildeIsQuasicoherentPieces k V)).toGradedAlgebra.toBase (specTopSite k) =
      Proj.toSpecZero ((schemeSheafGradedAlgebra (tildeOfModule k V)
          (tildeIsQuasicoherentPieces k V)).grading ⊤) ≫
        Spec.map (strZeroTop k V) ≫
        Spec.map (Scheme.ΓSpecIso (CommRingCat.of k)).inv := by
  have hfs : (isAffineOpen_top (Spec (CommRingCat.of k))).fromSpec =
      Spec.map (Scheme.ΓSpecIso (CommRingCat.of k)).inv := by
    rw [IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv]
  exact congrArg (fun g : Spec Γ(Spec (CommRingCat.of k), ⊤) ⟶ Spec (CommRingCat.of k) =>
    Proj.toSpecZero ((schemeSheafGradedAlgebra (tildeOfModule k V)
        (tildeIsQuasicoherentPieces k V)).grading ⊤) ≫
      Spec.map (strZeroTop k V) ≫ g) hfs

/-- **The projective space of `V` is the projective bundle of `V~`**, in the presentation of
`Stacks.SymGraded.schemeProjectiveBundle`: over the affine base `Spec k` the relative
homogeneous spectrum is the chart at the top open. -/
def projectiveSpaceOfModuleIsoSchemeProjectiveBundle :
    projectiveSpaceOfModule k V ≅
      (schemeProjectiveBundle (tildeOfModule k V) (tildeIsQuasicoherentPieces k V)).scheme :=
  projectiveSpaceOfModuleIsoProjTop k V ≪≫
    Stacks.FiniteMorphismProjective.projTopIso _ _

/-- **The identification with the projective bundle is one over `Spec k`.** -/
theorem projectiveSpaceOfModuleIsoSchemeProjectiveBundle_hom_comp_toBase :
    (projectiveSpaceOfModuleIsoSchemeProjectiveBundle k V).hom ≫
        (schemeProjectiveBundle (tildeOfModule k V)
          (tildeIsQuasicoherentPieces k V)).toBase =
      projectiveSpaceOfModuleToSpec k V := by
  have h1 : (Stacks.FiniteMorphismProjective.projTopIso
          (schemeSheafGradedAlgebra (tildeOfModule k V) (tildeIsQuasicoherentPieces k V))
          (schemeProjectiveBundle (tildeOfModule k V)
            (tildeIsQuasicoherentPieces k V))).hom ≫
        (schemeProjectiveBundle (tildeOfModule k V)
          (tildeIsQuasicoherentPieces k V)).toBase =
      (schemeSheafGradedAlgebra (tildeOfModule k V)
        (tildeIsQuasicoherentPieces k V)).toGradedAlgebra.toBase (specTopSite k) :=
    (Stacks.FiniteMorphismProjective.projTopIso_hom_toBase _ _).trans
      (GradedAlgebra.toOpen_ι _ (specTopSite k))
  have h2 : Proj.map (topGradedHom k V) (irrelevant_le_map_topGradedHom k V) ≫
      (schemeSheafGradedAlgebra (tildeOfModule k V)
        (tildeIsQuasicoherentPieces k V)).toGradedAlgebra.toBase (specTopSite k) =
      projectiveSpaceOfModuleToSpec k V := by
    rw [toBase_top_eq, Proj.map_toSpecZero_assoc]
    exact congrArg (fun g : Spec (CommRingCat.of ↥(SymPow.symmetricPower 0 k V)) ⟶
        Spec (CommRingCat.of k) =>
      Proj.toSpecZero (fun n : ℕ => SymPow.symmetricPower n k V) ≫ g)
      (specMap_gradedZeroRingHom_comp k V)
  refine Eq.trans (Category.assoc _ _ _) (Eq.trans ?_ h2)
  exact congrArg (fun m : Proj ((schemeSheafGradedAlgebra (tildeOfModule k V)
      (tildeIsQuasicoherentPieces k V)).grading ⊤) ⟶ Spec (CommRingCat.of k) =>
    Proj.map (topGradedHom k V) (irrelevant_le_map_topGradedHom k V) ≫ m) h1

/-- **Stacks Project, Tag 0FCY, clause (3).** Reading the `k`-module `V` as the quasi-coherent
`𝒪_{Spec k}`-module `V~`, the projective space `𝐏(V) = Proj(Sym_k V)` is the projective bundle
`𝐏(V~) = Proj_{Spec k}(Sym(V~))` of that module, by an isomorphism carrying the structure
morphism of `𝐏(V)` over `Spec k` to the projection of the bundle. -/
@[ega "II 4.1.1" "special case"]
theorem exists_iso_projectiveBundle_tildeOfModule :
    ∃ e : projectiveSpaceOfModule k V ≅
        Stacks.RelativeProj.projectiveBundle (Spec (CommRingCat.of k)) (tildeOfModule k V),
      e.hom ≫ Stacks.RelativeProj.projectiveBundleToBase (Spec (CommRingCat.of k))
          (tildeOfModule k V) =
        projectiveSpaceOfModuleToSpec k V := by
  obtain ⟨b, hb⟩ := projectiveBundlePresentationsAgree (tildeOfModule k V)
    (tildeIsQuasicoherentPieces k V)
  refine ⟨projectiveSpaceOfModuleIsoSchemeProjectiveBundle k V ≪≫ b, ?_⟩
  rw [Iso.trans_hom, Category.assoc, hb]
  exact projectiveSpaceOfModuleIsoSchemeProjectiveBundle_hom_comp_toBase k V

end AlgebraicGeometry

end
