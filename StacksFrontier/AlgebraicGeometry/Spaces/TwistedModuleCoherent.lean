module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.InvertibleCompare
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorCoherentOnSite
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorEncodings
public import StacksFrontier.AlgebraicGeometry.Ample.AmpleCriteria
public import StacksFrontier.AlgebraicGeometry.Divisors.TensorPower
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionStructureSheafCoherent
public import StacksFrontier.AlgebraicGeometry.Spaces.InvertibleCoherent
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulesAbelian
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperGlobalFunctions
public import StacksFrontier.AlgebraicGeometry.Topologies.CoherentSectionUniverseLift

/-!
# The twist of a module by tensor powers of invertible modules, and its coherence

Let `F` be an algebraic space over a scheme `S` contained in a big fppf site `B`, let `M` be an
`𝒪_F`-module and let `L₁, …, L_d` be invertible `𝒪_F`-modules.  This file constructs the twist

`M ⊗ L₁^{⊗ n₁} ⊗ ⋯ ⊗ L_d^{⊗ n_d}`

for an arbitrary integer exponent tuple, together with the reading of it in the module universe
in which the Euler characteristic of Stacks 0DN1 is taken, and proves that the twist of a
coherent module is coherent.

The coherence statement is what makes the intersection number of Stacks 0EDF an unconditional
definition.  It is assembled from three existing inputs and one new one:

* every integer tensor power of an invertible module is invertible, which is
  `Stacks.SheafOfModules.Invertible.tensorPower_isInvertible` (Stacks 01CT(1) and 01CU), and an
  invertible module on a locally Noetherian algebraic space is coherent on the small étale ringed
  site, which is `AlgebraicGeometry.Space.isCoherentOnSite_of_isInvertible` (Stacks 07UB);
* the tensor product of two modules coherent on a ringed site is coherent on it, which is
  `Stacks.SheafOfModules.TensorLocalProperties.tensorSheaf_isCoherentOnSite` (Stacks 03L6), and
  no local Noetherianity is needed for that step;
* raising the universe of the sections preserves coherence
  (`SheafOfModules.isCoherentOnSite_uliftForPresentation`) and quasi-coherence
  (`SheafOfModules.isQuasicoherentOnSite_uliftForPresentation'`).

Specialized to the direct image of the structure sheaf of a closed subspace of a proper algebraic
space over a field, this is `isCoherent_twistedModuleUlift_structureSheafPushforward`, whose two
geometric inputs are `AlgebraicGeometry.Space.isCoherent_structureSheafPushforward` — `i_*𝒪_Z` is
coherent — and `AlgebraicGeometry.Space.hasEtaleLocalProperty_isLocallyNoetherian_of_isProper` —
a proper algebraic space over a field is locally Noetherian.

## Main definitions

* `AlgebraicGeometry.Space.twistStep`: one twisting step `M ↦ M ⊗ L^{⊗ m}`.
* `AlgebraicGeometry.Space.twistedModule`: the twist by a finite family of invertible modules.
* `AlgebraicGeometry.Space.twistedModuleUlift`: the same module with the universe of its sections
  raised to the one in which the Euler characteristic lives.

## Main results

* `AlgebraicGeometry.Space.isCoherentOnSite_twistStep`: one twisting step preserves coherence on
  the small étale ringed site of a locally Noetherian algebraic space.
* `AlgebraicGeometry.Space.isCoherent_twistedModule` and
  `AlgebraicGeometry.Space.isCoherent_twistedModuleUlift`: **the twist of a coherent module by
  tensor powers of invertible modules is coherent**, before and after the universe lift of the
  sections.
* `AlgebraicGeometry.Space.isCoherent_twistedModuleUlift_structureSheafPushforward`: **the twists
  of `i_*𝒪_Z` are coherent**, for a closed immersion `i : Z ⟶ X` into a proper algebraic space
  over a field.  This is the statement the intersection number of Stacks 0EDF needs, and it is
  unconditional.

## Implementation notes

**The module universes.**  All of the module algebra happens at
`AlgebraicGeometry.Space.Modules.{u, u}`, the universe `u` of the structure rings: the tensor
product and the tensor powers of sheaves of modules are available only there, the sheafification
instances of the small étale ringed site being available for `AddCommGrpCat.{u}`.  The universe of
the sections is raised exactly once, by `SheafOfModules.uliftForPresentation`, in
`AlgebraicGeometry.Space.twistedModuleUlift`, because
`AlgebraicGeometry.Space.eulerCharacteristic` takes its module at `Modules.{u, max (u + 1) w}` —
the derived global sections of a ringed site take values in a module universe containing the
site.

**Why the twist is applied at an explicit site.**  The sheafification hypotheses of the tensor
product and of the tensor power are instances of the small étale ringed site only at the spelling
`(smallEtaleRingedSite … ).C` of the underlying category, with the `Category` instance carried by
that structure; inferring the category from `AlgebraicGeometry.Space.structurePresheaf` instead
produces the definitionally equal but syntactically different spelling
`AlgebraicGeometry.Space.SmallEtale`, at which instance search finds neither
`CategoryTheory.GrothendieckTopology.WEqualsLocallyBijective` nor
`CategoryTheory.HasWeakSheafify`, both being stated for the projections.
`AlgebraicGeometry.Space.twistStep` therefore applies the two constructions with the category and
the topology given explicitly, exactly as
`AlgebraicGeometry.Space.exists_cover_isRetractOfFiniteFree_of_isInvertible` does.

**Invertibility.**  Invertibility is `Stacks.SheafOfModules.IsInvertible`, which is the spelling
the small étale ringed site already uses in
`StacksFrontier.AlgebraicGeometry.Spaces.InvertibleCoherent`; the integer tensor power of
Stacks 01CU and the invertibility of its powers are stated over the duplicate class
`AlgebraicGeometry.SheafOfModules.IsInvertible`, and
`Stacks.SheafOfModules.IsInvertible.toAlgebraicGeometry` and its converse
`…ofAlgebraicGeometry` convert between them.

**No `@[stacks]` attribute.**  Coherence of a tensor product is the tensor clause of Stacks 07UE,
which `StacksFrontier/AlgebraicGeometry/Spaces/CoherentTensorProduct.lean` carries for the
mixed-universe tensor product `AlgebraicGeometry.Space.tensorModule`; what is proved here is the
iterated statement at the equi-universe spelling that the tensor powers of Stacks 01CU use, and
the invertible and structure-sheaf clauses of Stacks 07UB that feed it are carried in
`StacksFrontier/AlgebraicGeometry/Spaces/InvertibleCoherent.lean` and
`StacksFrontier/AlgebraicGeometry/Spaces/CoherentStructureSheaf.lean`.

## References

* [Stacks Project, Tag 01CU](https://stacks.math.columbia.edu/tag/01CU)
* [Stacks Project, Tag 01CT](https://stacks.math.columbia.edu/tag/01CT)
* [Stacks Project, Tag 03L6](https://stacks.math.columbia.edu/tag/03L6)
* [Stacks Project, Tag 03ZM](https://stacks.math.columbia.edu/tag/03ZM)
* [Stacks Project, Tag 04ZK](https://stacks.math.columbia.edu/tag/04ZK)
* [Stacks Project, Tag 07UA](https://stacks.math.columbia.edu/tag/07UA)
* [Stacks Project, Tag 07UB](https://stacks.math.columbia.edu/tag/07UB)
* [Stacks Project, Tag 07UE](https://stacks.math.columbia.edu/tag/07UE)
* [Stacks Project, Tag 0DN1](https://stacks.math.columbia.edu/tag/0DN1)
* [Stacks Project, Tag 0EDF](https://stacks.math.columbia.edu/tag/0EDF)
-/

@[expose] public noncomputable section

open CategoryTheory Limits

universe u w

namespace AlgebraicGeometry.Space

section Twist

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F)

/-- One twisting step on the small étale ringed site of the algebraic space `F`: the tensor
product of `M` with the `m`-th integer tensor power `L^{⊗ m}` of the invertible module `L`.

The tensor product is the sheafification of the tensor product of the underlying presheaves of
modules and the power is the one of Stacks 01CU.  The underlying category and the topology are
spelled as the projections of `AlgebraicGeometry.Space.smallEtaleRingedSite`, because that is
the spelling at which the sheafification instances of the site are stated; see the
implementation notes. -/
def twistStep (L : Modules.{u, u} B S hS F hF)
    [hL : Stacks.SheafOfModules.IsInvertible (structurePresheaf B S hS F)
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O).property L]
    (m : ℤ) (M : Modules.{u, u} B S hS F hF) : Modules.{u, u} B S hS F hF :=
  ((Stacks.SheafOfModules.Tensor.sheafTensor (smallEtaleRingedSite B S hS F hF).O).obj M).obj
    (@Stacks.SheafOfModules.Invertible.tensorPower.{u, u + 1, u}
      (smallEtaleRingedSite B S hS F hF).C _ (smallEtaleRingedSite B S hS F hF).J
      (structurePresheaf B S hS F)
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O).property _ _ L
      (Stacks.SheafOfModules.IsInvertible.toAlgebraicGeometry _ _ L hL) m)

/-- The twist `M ⊗ L₁^{⊗ n₁} ⊗ ⋯ ⊗ L_d^{⊗ n_d}` of a module by integer tensor powers of a
finite family of invertible modules, the factors being applied in the order of `Fin d`. -/
def twistedModule {d : ℕ} (M : Modules.{u, u} B S hS F hF)
    (L : Fin d → Modules.{u, u} B S hS F hF)
    [∀ j, Stacks.SheafOfModules.IsInvertible (structurePresheaf B S hS F)
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O).property (L j)]
    (n : Fin d → ℤ) : Modules.{u, u} B S hS F hF :=
  (List.finRange d).foldl (fun N j => twistStep B S hS F hF (L j) (n j) N) M

/-- The twist `M ⊗ L₁^{⊗ n₁} ⊗ ⋯ ⊗ L_d^{⊗ n_d}` with the universe of its sections raised to the
one in which the cohomology of an algebraic space over a scheme in `Type u` lives, so that its
Euler characteristic can be taken. -/
def twistedModuleUlift {d : ℕ} (M : Modules.{u, u} B S hS F hF)
    (L : Fin d → Modules.{u, u} B S hS F hF)
    [∀ j, Stacks.SheafOfModules.IsInvertible (structurePresheaf B S hS F)
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O).property (L j)]
    (n : Fin d → ℤ) : Modules.{u, max (u + 1) w} B S hS F hF :=
  SheafOfModules.uliftForPresentation.{u + 1, u, u, u, max (u + 1) w}
    (twistedModule B S hS F hF M L n)

/-! ### Coherence of the twists -/

/-- **An integer tensor power of an invertible module is coherent on the small étale ringed site
of a locally Noetherian algebraic space.**

Every tensor power of an invertible module is invertible, which is Stacks 01CT(1) and 01CU in the
form `Stacks.SheafOfModules.Invertible.tensorPower_isInvertible`, and an invertible module on a
locally Noetherian algebraic space is coherent on the site, which is the invertibility clause of
Stacks 07UB. -/
theorem isCoherentOnSite_tensorPower
    [Fact (HasEtaleLocalProperty B S hS F (fun V : Scheme.{u} => IsLocallyNoetherian V))]
    (L : Modules.{u, u} B S hS F hF)
    [hL : Stacks.SheafOfModules.IsInvertible (structurePresheaf B S hS F)
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O).property L]
    (m : ℤ) :
    SheafOfModules.IsCoherentOnSite
      (@Stacks.SheafOfModules.Invertible.tensorPower.{u, u + 1, u}
        (smallEtaleRingedSite B S hS F hF).C _ (smallEtaleRingedSite B S hS F hF).J
        (structurePresheaf B S hS F)
        (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O).property _ _ L
        (Stacks.SheafOfModules.IsInvertible.toAlgebraicGeometry _ _ L hL) m) :=
  isCoherentOnSite_of_isInvertible _
    (@Stacks.SheafOfModules.Invertible.tensorPower_isInvertible.{u, u + 1, u}
      (smallEtaleRingedSite B S hS F hF).C _ (smallEtaleRingedSite B S hS F hF).J
      (structurePresheaf B S hS F)
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O).property _ _ L
      hL m)

/-- **One twisting step preserves coherence on the small étale ringed site** of a locally
Noetherian algebraic space.

The tensor power is coherent by `isCoherentOnSite_tensorPower` and a tensor product of two
modules coherent on a ringed site is coherent on it, which is the coherent clause of
Stacks 03L6; that step needs no hypothesis on the space. -/
theorem isCoherentOnSite_twistStep
    [Fact (HasEtaleLocalProperty B S hS F (fun V : Scheme.{u} => IsLocallyNoetherian V))]
    (L : Modules.{u, u} B S hS F hF)
    [hL : Stacks.SheafOfModules.IsInvertible (structurePresheaf B S hS F)
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O).property L]
    (m : ℤ) (M : Modules.{u, u} B S hS F hF) (hM : SheafOfModules.IsCoherentOnSite M) :
    SheafOfModules.IsCoherentOnSite (twistStep B S hS F hF L m M) := by
  let _ := (smallEtaleRingedSite B S hS F hF).hasSheafCompose_forget₂_ringCat
  let _ := SheafOfModules.isLocallyInjective_id_structure
    (R := Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O)
  let _ := SheafOfModules.isLocallySurjective_id_structure
    (R := Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O)
  let : SheafOfModules.IsCoherentOnSite M := hM
  exact Stacks.SheafOfModules.TensorLocalProperties.tensorSheaf_isCoherentOnSite
    (smallEtaleRingedSite B S hS F hF) M _
    (hG := isCoherentOnSite_tensorPower B S hS F hF L m)

/-- Any chain of twisting steps preserves coherence on the small étale ringed site. -/
theorem isCoherentOnSite_foldl_twistStep
    [Fact (HasEtaleLocalProperty B S hS F (fun V : Scheme.{u} => IsLocallyNoetherian V))]
    {d : ℕ} (L : Fin d → Modules.{u, u} B S hS F hF)
    [∀ j, Stacks.SheafOfModules.IsInvertible (structurePresheaf B S hS F)
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O).property (L j)]
    (n : Fin d → ℤ) (l : List (Fin d)) (M : Modules.{u, u} B S hS F hF)
    (hM : SheafOfModules.IsCoherentOnSite M) :
    SheafOfModules.IsCoherentOnSite
      (l.foldl (fun N j => twistStep B S hS F hF (L j) (n j) N) M) := by
  induction l generalizing M with
  | nil => exact hM
  | cons j t ih =>
      exact ih _ (isCoherentOnSite_twistStep B S hS F hF (L j) (n j) M hM)

/-- **The twist of a module coherent on the small étale ringed site is coherent on that site.** -/
theorem isCoherentOnSite_twistedModule
    [Fact (HasEtaleLocalProperty B S hS F (fun V : Scheme.{u} => IsLocallyNoetherian V))]
    {d : ℕ} (M : Modules.{u, u} B S hS F hF) (L : Fin d → Modules.{u, u} B S hS F hF)
    [∀ j, Stacks.SheafOfModules.IsInvertible (structurePresheaf B S hS F)
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O).property (L j)]
    (n : Fin d → ℤ) (hM : SheafOfModules.IsCoherentOnSite M) :
    SheafOfModules.IsCoherentOnSite (twistedModule B S hS F hF M L n) :=
  isCoherentOnSite_foldl_twistStep B S hS F hF L n (List.finRange d) M hM

/-- **The twist of a coherent module by tensor powers of invertible modules is coherent.**  This
is `AlgebraicGeometry.Space.IsCoherent` of Stacks 07UA, which at this module universe follows
from coherence on the site. -/
theorem isCoherent_twistedModule
    [Fact (HasEtaleLocalProperty B S hS F (fun V : Scheme.{u} => IsLocallyNoetherian V))]
    {d : ℕ} (M : Modules.{u, u} B S hS F hF) (L : Fin d → Modules.{u, u} B S hS F hF)
    [∀ j, Stacks.SheafOfModules.IsInvertible (structurePresheaf B S hS F)
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O).property (L j)]
    (n : Fin d → ℤ) (hM : IsCoherent B S hS F hF M) :
    IsCoherent B S hS F hF (twistedModule B S hS F hF M L n) :=
  let : SheafOfModules.IsCoherentOnSite (twistedModule B S hS F hF M L n) :=
    isCoherentOnSite_twistedModule B S hS F hF M L n hM.toIsCoherentOnSite
  isCoherent_of_isCoherentOnSite B S hS F hF _

/-- **The twist of a coherent module, read in the module universe of the Euler characteristic, is
coherent.**

Raising the universe of the sections preserves coherence on the site by
`SheafOfModules.isCoherentOnSite_uliftForPresentation` and quasi-coherence by
`SheafOfModules.isQuasicoherentOnSite_uliftForPresentation'`. -/
theorem isCoherent_twistedModuleUlift
    [Fact (HasEtaleLocalProperty B S hS F (fun V : Scheme.{u} => IsLocallyNoetherian V))]
    {d : ℕ} (M : Modules.{u, u} B S hS F hF) (L : Fin d → Modules.{u, u} B S hS F hF)
    [∀ j, Stacks.SheafOfModules.IsInvertible (structurePresheaf B S hS F)
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O).property (L j)]
    (n : Fin d → ℤ) (hM : IsCoherent B S hS F hF M) :
    IsCoherent B S hS F hF (twistedModuleUlift.{u, w} B S hS F hF M L n) :=
  have h := isCoherent_twistedModule B S hS F hF M L n hM
  { __ := SheafOfModules.isQuasicoherentOnSite_uliftForPresentation'.{u + 1, u, u, u,
            max (u + 1) w} h.toIsQuasicoherentOnSite
    __ := SheafOfModules.isCoherentOnSite_uliftForPresentation.{u + 1, u, u, u, max (u + 1) w}
            _ h.toIsCoherentOnSite }

end Twist

/-! ### The twists of the direct image of the structure sheaf of a closed subspace -/

section Intersection

variable (k : Type u) [Field k] (B : BigFppfSite.{u}) (hk : B.Contains (Spec (.of k)))
    (X Z : AlgebraicSpaces B (Spec (.of k)) hk)

/-- **The twists of `i_*𝒪_Z` by tensor powers of invertible modules are coherent.**

Let `k` be a field, let `X` be a proper algebraic space over `k`, let `i : Z ⟶ X` be a closed
immersion and let `L₁, …, L_d` be invertible `𝒪_X`-modules.  Then
`i_*𝒪_Z ⊗ L₁^{⊗ n₁} ⊗ ⋯ ⊗ L_d^{⊗ n_d}` is a coherent `𝒪_X`-module for every integer exponent
tuple, in the module universe in which its Euler characteristic is taken.

`X` is locally Noetherian because it is proper over a field, which is Stacks 04ZK through
`AlgebraicGeometry.Space.hasEtaleLocalProperty_isLocallyNoetherian_of_isProper`; `i_*𝒪_Z` is then
coherent by `AlgebraicGeometry.Space.isCoherent_structureSheafPushforward`; and the twists of a
coherent module are coherent by `AlgebraicGeometry.Space.isCoherent_twistedModuleUlift`.

This is exactly what makes the intersection number of Stacks 0EDF an unconditional definition:
the Euler characteristics it sums are those of these modules. -/
theorem isCoherent_twistedModuleUlift_structureSheafPushforward {d : ℕ}
    (f : X.1 ⟶ yoneda.obj (baseObject k B hk)) (hf : IsProper B (Spec (.of k)) hk f)
    (i : Z ⟶ X) (hi : IsClosedImmersion B (Spec (.of k)) hk i.hom)
    (L : Fin d → Modules.{u, u} B (Spec (.of k)) hk X.1 X.2)
    [∀ j, Stacks.SheafOfModules.IsInvertible (structurePresheaf B (Spec (.of k)) hk X.1)
      (Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B (Spec (.of k)) hk X.1 X.2).O).property (L j)]
    (n : Fin d → ℤ) :
    IsCoherent B (Spec (.of k)) hk X.1 X.2
      (twistedModuleUlift.{u, w} B (Spec (.of k)) hk X.1 X.2
        (structureSheafPushforward B (Spec (.of k)) hk i) L n) :=
  have hX : HasEtaleLocalProperty B (Spec (.of k)) hk X.1
      (fun T : Scheme.{u} => IsLocallyNoetherian T) :=
    hasEtaleLocalProperty_isLocallyNoetherian_of_isProper k B hk X.1 X.2 f hf
  have : Fact (HasEtaleLocalProperty B (Spec (.of k)) hk X.1
      (fun V : Scheme.{u} => IsLocallyNoetherian V)) := ⟨hX⟩
  isCoherent_twistedModuleUlift.{u, w} B (Spec (.of k)) hk X.1 X.2 _ L n
    (isCoherent_structureSheafPushforward B (Spec (.of k)) hk hX i hi)

end Intersection

end AlgebraicGeometry.Space

end
