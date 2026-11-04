module

public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.RingTheory.LocalRing.Module
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.LocallyFreeRank
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.StalkwiseExactness
public import StacksFrontier.Algebra.Homology.StrictlyPerfectRestrictionOfLE
public import StacksFrontier.Topology.Sheaves.Cohomology.PerfectComplexes.BasicProperties
public import StacksFrontier.Topology.Sheaves.Cohomology.PerfectComplexes.FiniteFreeRepresentation
public import StacksFrontier.Topology.Sheaves.Cohomology.PerfectComplexes.OpcyclesFinitePresentation
public import StacksFrontier.Topology.Sheaves.Modules.LocallyFreeRetract
public import StacksFrontier.Topology.Sheaves.Modules.StalkAcyclic
import StacksCore.Tactic.StacksAttribute

/-!
# The finite free cohomology locus

Let `(X, 𝒪_X)` be a ringed space and let `E` be an object of the derived category of
`𝒪_X`-modules. The *finite free cohomology locus* of `E` is the set of points `x` at which every
cohomology stalk `H^i(E)_x` is a finite free `𝒪_{X, x}`-module. Tag 0GT1 asserts, for `E` perfect
and all stalks `𝒪_{X, x}` local rings, that this set is open and is the largest open set on which
all the cohomology sheaves `H^i(E)` are finite locally free.

This file defines the locus, proves that it is open, and proves the maximality half: an open set
over which every cohomology sheaf is finite locally free is contained in the locus, because a
module that is free of finite rank on a neighbourhood of a point has finite free stalk there.

## Main definitions

* `AlgebraicGeometry.RingedSpace.IsFiniteLocallyFreeOver`: an `𝒪_X`-module is finite locally free
  over an open set when each of its points has a neighbourhood inside that open set on which the
  restriction of the module is isomorphic to a free module of finite rank.
* `AlgebraicGeometry.RingedSpace.cohomologyFiniteFreeLocus`: the points at which every cohomology
  stalk of a derived object is a finite free module over the local ring.

## Main results

* `AlgebraicGeometry.RingedSpace.freeAndFinite_stalk_of_isFiniteLocallyFreeOver`: a module that is
  finite locally free over an open set has finite free stalks at the points of that open set.
* `AlgebraicGeometry.RingedSpace.isOpen_cohomologyFiniteFreeLocus`: the openness half of
  [Stacks, Tag 0GT1].
* `AlgebraicGeometry.RingedSpace.subset_cohomologyFiniteFreeLocus`: the maximality half of
  [Stacks, Tag 0GT1].

## Implementation notes

Finite local freeness over an open set is phrased through the restriction functor
`StrictlyPerfect.restrictModules` of the perfect-complex interface, as the existence of free
charts on a neighbourhood of each point. That restriction is the same functor as
`LocallyFreeRank.restrictMod`, so a free chart is literally a `LocallyFreeRank.Trivialization`,
and [Stacks, Tag 01C9] supplies the semilinear stalk comparison
`LocallyFreeRank.Trivialization.stalk_linearEquiv_finsupp`: a trivialisation of a module over an
open set computes the stalk at each of its points as a free module on the trivialising index set.
A finite index set therefore yields a finite basis of the stalk.

The stalk of an `𝒪_X`-module is a module over the stalk `𝒪_{X, x}` of the *commutative* structure
sheaf, which is the ring the local-ring hypothesis of the tag speaks about; the instance is named
because instance search does not fire through the forgetful wrapper by which the base sheaf of
rings of an `𝒪_X`-module is built.

Openness is local and is proved on the local strictly perfect models supplied by
[Stacks, Tag 08CM]. Two comparisons carry the statement between a model and the ambient space.
The first, `freeAndFiniteStalk_restrictModules_iff`, says that finite freeness of a stalk is
unchanged by restriction to an open set: the stalk of the restriction is the ambient stalk
semilinearly over `LocallyFreeRank.restrictStalkRingEquiv`, which is [Stacks, Tag 01C9] again.
The second, `localModelHomologyIso`, identifies the cohomology of a local model with the
restriction of the cohomology sheaf, by exactness of restriction and the factorisation of the
derived cohomology functor through the cohomology of complexes.

On a model `P` the argument passes through the opcycles `Coker(d^{j - 1})`, which are of finite
presentation. At the stalk of a local ring, the cohomology and the opcycles of `P` determine each
other: the degree-`i` cohomology stalk is the kernel of the map out of the degree-`i` opcycles
stalk, and the two short exact sequences attached to that map split as soon as the terms and the
opcycles one degree up are projective. So finite freeness of all the cohomology stalks at a point
gives finite freeness of all the opcycles stalks there, [Stacks, Tag 0B8J] makes the opcycles free
on a neighbourhood, and over that neighbourhood the implication runs back.

Stalks are read over two rings: the `CommRingCat`-valued stalk `𝒪_{X, x}`, which the statement of
the tag and the local-ring hypothesis speak about, and the `RingCat`-valued stalk of the structure
sheaf of rings, over which the exact stalk functor on sheaves of modules is stated. The two agree
through `SemilinearStalk.commStalkRingEquiv`, and `freeAndFinite_iff_of_ringEquiv` transports
finite freeness along such a comparison.

All universes coincide, as they must for `StrictlyPerfect.OXMod` to exist; the universe of the
derived category is left free.

## References

* [Stacks Project, Tag 0GT1](https://stacks.math.columbia.edu/tag/0GT1)
* [Stacks Project, Tag 01C9](https://stacks.math.columbia.edu/tag/01C9)
* [Stacks Project, Tag 08CM](https://stacks.math.columbia.edu/tag/08CM)
* [Stacks Project, Tag 0B8J](https://stacks.math.columbia.edu/tag/0B8J)
* [Stacks Project, Tag 0BCI](https://stacks.math.columbia.edu/tag/0BCI)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace StrictlyPerfect

namespace AlgebraicGeometry.RingedSpace

universe u d w w'

variable {X : RingedSpace.{u, u}}

/-- The `𝒪_{X, x}`-module structure on the stalk at `x` of an `𝒪_X`-module. This is Mathlib's
presheaf-of-modules stalk-module instance, named because instance search does not fire through
the forgetful wrapper by which `StrictlyPerfect.structureSheafOfRings` is built. -/
instance moduleStalk (M : OXMod.{u, u} X) (x : X.carrier) :
    Module (ToType (X.presheaf.stalk x))
      (ToType (TopCat.Presheaf.stalk M.val.presheaf x)) :=
  LocallyFreeRank.instModuleStalkF X.carrier X.sheaf M x

/-- An `𝒪_X`-module is *finite locally free over* an open set `V` when every point of `V` has an
open neighbourhood inside `V` on which the restriction of the module is isomorphic to a free
module on a finite index set. -/
def IsFiniteLocallyFreeOver (M : OXMod.{u, u} X) (V : Opens X.carrier) : Prop :=
  ∀ x ∈ V, ∃ W : Opens X.carrier, x ∈ W ∧ W ≤ V ∧ ∃ ι : Type u, Finite ι ∧
    Nonempty ((restrictModules X W).obj M ≅ _root_.SheafOfModules.free.{u} ι)

/-- A free chart of an `𝒪_X`-module over an open set is a trivialisation of it there, the two
notions of restriction to an open subspace being the same. -/
private def trivializationOfIsoFree {M : OXMod.{u, u} X} {W : Opens X.carrier} {ι : Type u}
    (e : (restrictModules X W).obj M ≅ _root_.SheafOfModules.free.{u} ι) :
    LocallyFreeRank.Trivialization X.carrier (structureSheafOfRings X) M W :=
  ⟨ι, e⟩

/-- A trivialisation of an `𝒪_X`-module over a finite index set makes its stalks free of finite
rank at every point of the open set. -/
private theorem free_and_finite_stalk_of_trivialization {M : OXMod.{u, u} X} {V : Opens X.carrier}
    (τ : LocallyFreeRank.Trivialization X.carrier (structureSheafOfRings X) M V) [Finite τ.ι]
    {x : X.carrier} (hx : x ∈ V) :
    Module.Free (ToType (X.presheaf.stalk x))
        (ToType (TopCat.Presheaf.stalk M.val.presheaf x)) ∧
      Module.Finite (ToType (X.presheaf.stalk x))
        (ToType (TopCat.Presheaf.stalk M.val.presheaf x)) := by
  let _ : Module (ToType (TopCat.Presheaf.stalk X.sheaf.obj x))
      (ToType (TopCat.Presheaf.stalk M.val.presheaf x)) := moduleStalk M x
  obtain ⟨eStalk⟩ :=
    LocallyFreeRank.Trivialization.stalk_linearEquiv_finsupp X.carrier X.sheaf M x hx τ
  have b : Module.Basis τ.ι (ToType (TopCat.Presheaf.stalk X.sheaf.obj x))
      (ToType (TopCat.Presheaf.stalk M.val.presheaf x)) := Module.Basis.ofRepr eStalk
  exact ⟨Module.Free.of_basis b, Module.Finite.of_basis b⟩

/-- At a point of an open set over which an `𝒪_X`-module is finite locally free, the stalk is a
free module of finite rank over the local ring of the space. -/
theorem freeAndFinite_stalk_of_isFiniteLocallyFreeOver {M : OXMod.{u, u} X}
    {V : Opens X.carrier} (hM : IsFiniteLocallyFreeOver M V) {x : X.carrier} (hx : x ∈ V) :
    Module.Free (ToType (X.presheaf.stalk x))
        (ToType (TopCat.Presheaf.stalk M.val.presheaf x)) ∧
      Module.Finite (ToType (X.presheaf.stalk x))
        (ToType (TopCat.Presheaf.stalk M.val.presheaf x)) := by
  obtain ⟨W, hxW, -, ι, hfin, ⟨e⟩⟩ := hM x hx
  have _ : Finite (trivializationOfIsoFree e).ι := hfin
  exact free_and_finite_stalk_of_trivialization (trivializationOfIsoFree e) hxW

/-- **The finite free cohomology locus of a derived object.** These are the points at which every
cohomology stalk `H^i(E)_x` is a finite free `𝒪_{X, x}`-module. -/
@[stacks 0GT1 "the locus"]
def cohomologyFiniteFreeLocus [HasDerivedCategory.{d} (OXMod.{u, u} X)]
    (E : DerivedCategory (OXMod.{u, u} X)) : Set X.carrier :=
  {x | ∀ i : ℤ,
    Module.Free (ToType (X.presheaf.stalk x))
        (ToType (TopCat.Presheaf.stalk
          ((DerivedCategory.homologyFunctor (OXMod.{u, u} X) i).obj E).val.presheaf x)) ∧
      Module.Finite (ToType (X.presheaf.stalk x))
        (ToType (TopCat.Presheaf.stalk
          ((DerivedCategory.homologyFunctor (OXMod.{u, u} X) i).obj E).val.presheaf x))}

/-- A point lies in the finite free cohomology locus exactly when all the cohomology stalks there
are finite free. -/
theorem mem_cohomologyFiniteFreeLocus_iff [HasDerivedCategory.{d} (OXMod.{u, u} X)]
    (E : DerivedCategory (OXMod.{u, u} X)) (x : X.carrier) :
    x ∈ cohomologyFiniteFreeLocus E ↔ ∀ i : ℤ,
      Module.Free (ToType (X.presheaf.stalk x))
          (ToType (TopCat.Presheaf.stalk
            ((DerivedCategory.homologyFunctor (OXMod.{u, u} X) i).obj E).val.presheaf x)) ∧
        Module.Finite (ToType (X.presheaf.stalk x))
          (ToType (TopCat.Presheaf.stalk
            ((DerivedCategory.homologyFunctor (OXMod.{u, u} X) i).obj E).val.presheaf x)) :=
  Iff.rfl

/-- **Stacks 0GT1, maximality.** Every open set over which all the cohomology sheaves of a derived
object are finite locally free is contained in the finite free cohomology locus: finite local
freeness near a point makes the cohomology stalks there finite free. -/
@[stacks 0GT1 "maximality of the locus"]
theorem subset_cohomologyFiniteFreeLocus [HasDerivedCategory.{d} (OXMod.{u, u} X)]
    (E : DerivedCategory (OXMod.{u, u} X)) (V : Opens X.carrier)
    (hV : ∀ i : ℤ, IsFiniteLocallyFreeOver
      ((DerivedCategory.homologyFunctor (OXMod.{u, u} X) i).obj E) V) :
    (V : Set X.carrier) ⊆ cohomologyFiniteFreeLocus E := fun _ hx i =>
  freeAndFinite_stalk_of_isFiniteLocallyFreeOver (hV i) hx

/-! ### Splittings and projectivity in an abelian category

The homological input is the pair of short exact sequences attached to a morphism `f`: the
kernel of `f` sits inside the source with quotient the coimage of `f`, and the image of `f` sits
inside the target with quotient the cokernel of `f`. Applied to the map `Coker(d^{i-1}) ⟶ P^{i+1}`
induced by a differential, they relate the cohomology, the opcycles and the terms of a complex.
-/

section Abelian

variable {C : Type w'} [Category.{w} C] [Abelian C]

/-- The coimage of a morphism whose target and whose cokernel are projective is projective: the
image sits inside the target with projective quotient, so it is a direct summand of it. -/
private theorem projective_coimage {A B : C} (f : A ⟶ B) [Projective B]
    [Projective (cokernel f)] : Projective (Abelian.coimage f) :=
  have hS : (ShortComplex.mk (kernel.ι (cokernel.π f)) (cokernel.π f)
      (kernel.condition _)).ShortExact := { exact := ShortComplex.exact_kernel (cokernel.π f) }
  Projective.of_iso (Abelian.coimageIsoImage f).symm
    (Retract.projective (X := Abelian.image f) (Y := B)
      ⟨kernel.ι (cokernel.π f), hS.splittingOfProjective.r, hS.splittingOfProjective.f_r⟩)

/-- The kernel of a morphism sits inside its source as a short exact sequence with quotient the
coimage of the morphism. -/
private theorem shortExact_kernel_coimage {A B : C} (f : A ⟶ B) :
    (ShortComplex.mk (kernel.ι f) (cokernel.π (kernel.ι f))
      (cokernel.condition _)).ShortExact :=
  { exact := ShortComplex.exact_cokernel (kernel.ι f) }

variable (K : CochainComplex C ℤ)

/-- The cokernel of the map `Coker(d^{i-1}) ⟶ K^{i+1}` out of the degree-`i` opcycles is the
degree-`i+1` opcycles: that map and the differential `d^i` have the same cokernel, the
projection onto the opcycles being an epimorphism. -/
private def cokernelFromOpcyclesIso (i : ℤ) :
    cokernel (K.fromOpcycles i (i + 1)) ≅ K.opcycles (i + 1) :=
  (cokernelEpiComp (K.pOpcycles i) (K.fromOpcycles i (i + 1))).symm ≪≫
    cokernelIsoOfEq (K.p_fromOpcycles i (i + 1)) ≪≫
    IsColimit.coconePointUniqueUpToIso (cokernelIsCokernel (K.d i (i + 1)))
      (K.opcyclesIsCokernel i (i + 1) (by rw [CochainComplex.prev]; omega))

/-- The degree-`i` cohomology of a complex is the kernel of the map out of the degree-`i`
opcycles induced by the differential `d^i`. -/
private def homologyIsoKernelFromOpcycles (i : ℤ) :
    K.homology i ≅ kernel (K.fromOpcycles i (i + 1)) :=
  IsLimit.conePointUniqueUpToIso
    (K.homologyIsKernel i (i + 1) (by rw [CochainComplex.next]))
    (limit.isLimit (parallelPair (K.fromOpcycles i (i + 1)) 0))

/-- If the degree-`i+1` term and the degree-`i+1` opcycles of a complex are projective, then the
coimage of the map out of the degree-`i` opcycles is projective. -/
private theorem projective_coimage_fromOpcycles (i : ℤ)
    [Projective (K.X (i + 1))] [hC : Projective (K.opcycles (i + 1))] :
    Projective (Abelian.coimage (K.fromOpcycles i (i + 1))) :=
  have _ : Projective (cokernel (K.fromOpcycles i (i + 1))) :=
    Projective.of_iso (cokernelFromOpcyclesIso K i).symm hC
  projective_coimage (K.fromOpcycles i (i + 1))

/-- Under the same hypotheses, the sequence `ker → opcycles^i → coim` splits. -/
private def splitting_kernel_coimage_fromOpcycles (i : ℤ)
    [Projective (K.X (i + 1))] [Projective (K.opcycles (i + 1))] :
    (ShortComplex.mk (kernel.ι (K.fromOpcycles i (i + 1)))
      (cokernel.π (kernel.ι (K.fromOpcycles i (i + 1)))) (cokernel.condition _)).Splitting :=
  have _ := projective_coimage_fromOpcycles K i
  (shortExact_kernel_coimage (K.fromOpcycles i (i + 1))).splittingOfProjective

/-- If the degree-`i+1` term and the degree-`i+1` opcycles of a complex are projective, then the
degree-`i` cohomology is a retract of the degree-`i` opcycles. -/
private theorem nonempty_retract_homology_opcycles (i : ℤ)
    (hX : Projective (K.X (i + 1))) (hC : Projective (K.opcycles (i + 1))) :
    Nonempty (Retract (K.homology i) (K.opcycles i)) := by
  have _ := hX
  have _ := hC
  let hsp := splitting_kernel_coimage_fromOpcycles K i
  exact ⟨(homologyIsoKernelFromOpcycles K i).retract.trans ⟨kernel.ι _, hsp.r, hsp.f_r⟩⟩

/-- Descending step for the projectivity of the opcycles: the degree-`i` opcycles is an
extension of the coimage of `d^i` by the degree-`i` cohomology, and that extension splits. -/
private theorem projective_opcycles_step (i : ℤ)
    (hX : Projective (K.X (i + 1))) (hC : Projective (K.opcycles (i + 1)))
    (hH : Projective (K.homology i)) : Projective (K.opcycles i) := by
  have _ := hX
  have _ := hC
  have _ : Projective (kernel (K.fromOpcycles i (i + 1))) :=
    Projective.of_iso (homologyIsoKernelFromOpcycles K i) hH
  have _ := projective_coimage_fromOpcycles K i
  exact Projective.of_iso (splitting_kernel_coimage_fromOpcycles K i).isoBinaryBiproduct.symm
    inferInstance

/-- The opcycles in a degree whose term vanishes vanish, hence are projective. -/
private theorem projective_opcycles_of_isZero (i : ℤ) (h : IsZero (K.X i)) :
    Projective (K.opcycles i) :=
  Projective.of_iso ((K.sc i).opcyclesIsoX₂ (h.eq_of_tgt _ _)).symm
    (Projective.of_iso h.isoZero.symm inferInstance)

/-- **All opcycles of a complex with projective terms and projective cohomology are
projective**, provided the complex vanishes in high degrees: descend from a degree above the
bound, where the opcycles vanish. -/
private theorem projective_opcycles (b : ℤ)
    (hzero : ∀ n : ℤ, b < n → IsZero (K.X n))
    (hX : ∀ n : ℤ, Projective (K.X n))
    (hH : ∀ n : ℤ, Projective (K.homology n)) (i : ℤ) :
    Projective (K.opcycles i) := by
  have aux : ∀ m : ℕ, ∀ n : ℤ, b + 1 - n ≤ (m : ℤ) → Projective (K.opcycles n) := by
    intro m
    induction m with
    | zero =>
      intro n hn
      exact projective_opcycles_of_isZero K n (hzero n (by omega))
    | succ m ih =>
      intro n hn
      exact projective_opcycles_step K n (hX (n + 1)) (ih (n + 1) (by omega)) (hH n)
  exact aux (b + 1 - i).toNat i (by omega)

end Abelian

/-! ### Finite freeness of a stalk over the two spellings of the stalk ring

The stalk of an `𝒪_X`-module carries two actions of scalars: one by the `RingCat`-valued stalk of
the structure sheaf of rings, over which the exact stalk functor on sheaves of modules is stated,
and one by the `CommRingCat`-valued stalk `𝒪_{X, x}`, over which the finite free locus and the
local-ring hypothesis are stated. They agree through `SemilinearStalk.commStalkRingEquiv`.
-/

/-- The stalk of the structure sheaf of rings at a point, as a (not necessarily commutative)
ring. This is the ring over which the stalk functor on sheaves of modules is stated. -/
abbrev ringCatStalk (X : RingedSpace.{u, u}) (x : X.carrier) : Type u :=
  ToType (TopCat.Presheaf.stalk (C := RingCat.{u}) (structureSheafOfRings X).obj x)

/-- Taking the stalk at a point of an `𝒪_X`-module, as an exact functor to modules over the
`RingCat`-valued stalk of the structure sheaf of rings. -/
abbrev moduleStalkFunctor (X : RingedSpace.{u, u}) (x : X.carrier) :
    OXMod.{u, u} X ⥤ ModuleCat.{u} (TopCat.Presheaf.stalk (C := RingCat.{u})
      (structureSheafOfRings X).obj x) :=
  AlgebraicGeometry.SheafOfModules.stalkFunctor (structureSheafOfRings X) x

/-- The comparison isomorphism between the `RingCat`-valued and the `CommRingCat`-valued stalk
of the structure sheaf at a point. -/
def ringCatStalkEquiv (X : RingedSpace.{u, u}) (x : X.carrier) :
    ringCatStalk X x ≃+* ToType (X.presheaf.stalk x) :=
  SemilinearStalk.commStalkRingEquiv X.presheaf x

/-- The stalk of an `𝒪_X`-module at a point is a free module of finite rank over the stalk of
the structure sheaf. This is the condition defining the finite free cohomology locus. -/
def FreeAndFiniteStalk (M : OXMod.{u, u} X) (x : X.carrier) : Prop :=
  Module.Free (ToType (X.presheaf.stalk x))
      (ToType (TopCat.Presheaf.stalk M.val.presheaf x)) ∧
    Module.Finite (ToType (X.presheaf.stalk x))
      (ToType (TopCat.Presheaf.stalk M.val.presheaf x))

/-- The two stalk-ring actions on the stalk of an `𝒪_X`-module agree through the comparison
isomorphism. -/
theorem smul_ringCatStalkEquiv (M : OXMod.{u, u} X) (x : X.carrier)
    (s : ringCatStalk X x) (m : ToType (TopCat.Presheaf.stalk M.val.presheaf x)) :
    ringCatStalkEquiv X x s • m = s • m :=
  AlgebraicGeometry.SheafOfModules.commStalkRingEquiv_smul_eq' X.sheaf x M.val s m

/-- The inverse comparison isomorphism also matches the two stalk-ring actions. -/
theorem smul_ringCatStalkEquiv_symm (M : OXMod.{u, u} X) (x : X.carrier)
    (c : ToType (X.presheaf.stalk x))
    (m : ToType (TopCat.Presheaf.stalk M.val.presheaf x)) :
    (ringCatStalkEquiv X x).symm c • m = c • m :=
  ((ringCatStalkEquiv X x).apply_symm_apply c ▸
    smul_ringCatStalkEquiv M x ((ringCatStalkEquiv X x).symm c) m).symm

/-- Finite freeness transports along a linear equivalence that is semilinear over a ring
isomorphism acting compatibly on the target: a basis is carried across and its coefficients are
transported by `Module.Basis.mapCoeffs`. -/
private theorem freeAndFinite_iff_of_ringEquiv
    {R S : Type u} [Ring R] [Ring S] [Nontrivial S]
    {A B : Type u} [AddCommGroup A] [AddCommGroup B]
    [instMRA : Module R A] [instMRB : Module R B] [instMSB : Module S B]
    (f : R ≃+* S) (hsm : ∀ (c : R) (b : B), f c • b = c • b) (ea : A ≃ₗ[R] B) :
    (Module.Free R A ∧ Module.Finite R A) ↔ (Module.Free S B ∧ Module.Finite S B) := by
  classical
  have _ : Nontrivial R := f.toEquiv.nontrivial
  refine ⟨fun ⟨_, _⟩ => ?_, fun ⟨_, _⟩ => ?_⟩
  · have b := Module.Free.chooseBasis R A
    have _ : Finite (Module.Free.ChooseBasisIndex R A) := Module.Finite.finite_basis b
    have b3 := (b.map ea).mapCoeffs f hsm
    exact ⟨Module.Free.of_basis b3, Module.Finite.of_basis b3⟩
  · have b := Module.Free.chooseBasis S B
    have _ : Finite (Module.Free.ChooseBasisIndex S B) := Module.Finite.finite_basis b
    have b3 := (b.mapCoeffs f.symm (fun c x => by
      rw [← hsm (f.symm c) x, RingEquiv.apply_symm_apply])).map ea.symm
    exact ⟨Module.Free.of_basis b3, Module.Finite.of_basis b3⟩

/-- A stalk is finite free over `𝒪_{X, x}` exactly when it is finite free over the
`RingCat`-valued stalk of the structure sheaf of rings. -/
private theorem freeAndFiniteStalk_iff (M : OXMod.{u, u} X) (x : X.carrier)
    [Nontrivial (ToType (X.presheaf.stalk x))] :
    FreeAndFiniteStalk M x ↔
      (Module.Free (ringCatStalk X x) (ToType (TopCat.Presheaf.stalk M.val.presheaf x)) ∧
        Module.Finite (ringCatStalk X x)
          (ToType (TopCat.Presheaf.stalk M.val.presheaf x))) :=
  (freeAndFinite_iff_of_ringEquiv (ringCatStalkEquiv X x) (smul_ringCatStalkEquiv M x)
    (LinearEquiv.refl (ringCatStalk X x)
      (ToType (TopCat.Presheaf.stalk M.val.presheaf x)))).symm

/-- A morphism of stalk modules over the `RingCat`-valued stalk ring is `𝒪_{X, x}`-linear, the
two actions agreeing through the comparison isomorphism. -/
def stalkLinearMapOfHom {M N : OXMod.{u, u} X} {x : X.carrier}
    (φ : (moduleStalkFunctor X x).obj M ⟶ (moduleStalkFunctor X x).obj N) :
    ToType (TopCat.Presheaf.stalk M.val.presheaf x) →ₗ[ToType (X.presheaf.stalk x)]
      ToType (TopCat.Presheaf.stalk N.val.presheaf x) where
  toFun := φ.hom
  map_add' a b := map_add φ.hom a b
  map_smul' c m :=
    (congrArg φ.hom (smul_ringCatStalkEquiv_symm M x c m).symm).trans
      ((map_smul φ.hom ((ringCatStalkEquiv X x).symm c) m).trans
        (smul_ringCatStalkEquiv_symm N x c (φ.hom m)))

/-- `stalkLinearMapOfHom` has the same underlying function as the morphism it comes from. -/
@[simp]
private theorem stalkLinearMapOfHom_apply {M N : OXMod.{u, u} X} {x : X.carrier}
    (φ : (moduleStalkFunctor X x).obj M ⟶ (moduleStalkFunctor X x).obj N)
    (m : ToType (TopCat.Presheaf.stalk M.val.presheaf x)) :
    stalkLinearMapOfHom φ m = φ.hom m := rfl

/-- Finite freeness of a stalk only depends on the isomorphism class of the module. -/
private theorem freeAndFiniteStalk_of_iso {M N : OXMod.{u, u} X} (e : M ≅ N) (x : X.carrier)
    [Nontrivial (ToType (X.presheaf.stalk x))] (h : FreeAndFiniteStalk M x) :
    FreeAndFiniteStalk N x := by
  rw [freeAndFiniteStalk_iff] at h ⊢
  obtain ⟨hf, hfin⟩ := h
  have _ := hf
  have _ := hfin
  have φ : ToType (TopCat.Presheaf.stalk M.val.presheaf x) ≃ₗ[ringCatStalk X x]
      ToType (TopCat.Presheaf.stalk N.val.presheaf x) :=
    ((moduleStalkFunctor X x).mapIso e).toLinearEquiv
  exact ⟨Module.Free.of_equiv φ, Module.Finite.equiv φ⟩

/-- A free chart of an `𝒪_X`-module over an open set, in the slice-category spelling of
restriction, is a trivialisation of it there. -/
private def trivializationOfOverIsoFree {M : OXMod.{u, u} X} {V : Opens X.carrier}
    {ι : Type u} (e : M.over V ≅ _root_.SheafOfModules.free.{u} ι) :
    LocallyFreeRank.Trivialization X.carrier (structureSheafOfRings X) M V where
  ι := ι
  iso :=
    (Iso.refl (LocallyFreeRank.restrictMod X.carrier V (structureSheafOfRings X) M) :
        LocallyFreeRank.restrictMod X.carrier V (structureSheafOfRings X) M ≅
          (V.sheafOfModulesEquivOver (structureSheafOfRings X)).functor.obj (M.over V)) ≪≫
      (V.sheafOfModulesEquivOver (structureSheafOfRings X)).functor.mapIso e ≪≫
      (_root_.SheafOfModules.mapFreeIso
        (V.sheafOfModulesEquivOver (structureSheafOfRings X)).functor ι
        (V.sheafOfModulesEquivOverUnit (structureSheafOfRings X))).symm

/-- An `𝒪_X`-module with a free chart on a finite index set over an open set has finite free
stalks at every point of that open set, by [Stacks, Tag 01C9]. -/
private theorem freeAndFiniteStalk_of_overIsoFree {M : OXMod.{u, u} X} {V : Opens X.carrier}
    {ι : Type u} [Finite ι] (e : M.over V ≅ _root_.SheafOfModules.free.{u} ι)
    {y : X.carrier} (hy : y ∈ V) : FreeAndFiniteStalk M y := by
  have _ : Finite (trivializationOfOverIsoFree e).ι := ‹Finite ι›
  exact free_and_finite_stalk_of_trivialization (trivializationOfOverIsoFree e) hy

/-- On a space with local stalks, a direct summand of a finite free `𝒪_X`-module has finite free
stalks, by [Stacks, Tag 0BCI]. -/
private theorem freeAndFiniteStalk_of_isDirectSummandOfFiniteFree
    [hloc : ∀ z : X.carrier, IsLocalRing (ToType (X.presheaf.stalk z))]
    {M : OXMod.{u, u} X} (hM : IsDirectSummandOfFiniteFree M) (x : X.carrier) :
    FreeAndFiniteStalk M x := by
  have _ : ∀ z : X.carrier, IsLocalRing (ToType (TopCat.Presheaf.stalk X.sheaf.obj z)) := hloc
  obtain ⟨n, ⟨ρ⟩⟩ := AlgebraicGeometry.RingedSpace.exists_retract_free hM
  obtain ⟨r, ⟨eq⟩⟩ := AlgebraicGeometry.SheafOfModules.exists_free_stalk_of_retract
    (X := X.carrier) (O := X.sheaf) ρ
    (isFiniteLocallyFree_of_iso (finiteFreeIsoFree X n).symm
      (isFiniteLocallyFree_finiteFree X n)) x
  have b : Module.Basis (ULift.{u} (Fin r)) (ringCatStalk X x)
      (ToType (TopCat.Presheaf.stalk M.val.presheaf x)) := Module.Basis.ofRepr eq
  exact (freeAndFiniteStalk_iff M x).mpr ⟨Module.Free.of_basis b, Module.Finite.of_basis b⟩

/-- A module with free stalk at a point is a projective object of the category of modules over
the stalk ring there. -/
private theorem projective_moduleStalkFunctor_obj {M : OXMod.{u, u} X} {x : X.carrier}
    (h : Module.Free (ringCatStalk X x) (ToType (TopCat.Presheaf.stalk M.val.presheaf x))) :
    Projective ((moduleStalkFunctor X x).obj M) :=
  ModuleCat.projective_of_free (R := ringCatStalk X x) (M := (moduleStalkFunctor X x).obj M)
    (Module.Free.chooseBasis (ringCatStalk X x)
      (ToType (TopCat.Presheaf.stalk M.val.presheaf x)))

/-- The complex of stalks at a point of a complex of `𝒪_X`-modules. -/
private abbrev stalkComplex (P : CochainComplex (OXMod.{u, u} X) ℤ) (x : X.carrier) :
    CochainComplex (ModuleCat.{u} (TopCat.Presheaf.stalk (C := RingCat.{u})
      (structureSheafOfRings X).obj x)) ℤ :=
  ((moduleStalkFunctor X x).mapHomologicalComplex (ComplexShape.up ℤ)).obj P

/-- The stalk functor is exact, so the cohomology of the complex of stalks is the stalk of the
cohomology. -/
private def stalkComplexHomologyIso (P : CochainComplex (OXMod.{u, u} X) ℤ) (x : X.carrier)
    (i : ℤ) : (stalkComplex P x).homology i ≅ (moduleStalkFunctor X x).obj (P.homology i) :=
  (P.sc i).mapHomologyIso (moduleStalkFunctor X x)

/-- The stalk functor is exact, so the opcycles of the complex of stalks are the stalk of the
opcycles. -/
private def stalkComplexOpcyclesIso (P : CochainComplex (OXMod.{u, u} X) ℤ) (x : X.carrier)
    (i : ℤ) : (stalkComplex P x).opcycles i ≅ (moduleStalkFunctor X x).obj (P.opcycles i) :=
  (P.sc i).mapOpcyclesIso (moduleStalkFunctor X x)

/-- If the stalk functor images of `𝒪_X`-modules `M` and `N` form a retract and `N` has a finite
free stalk at `x` over a local ring, then so does `M`. -/
private theorem freeAndFiniteStalk_of_stalkRetract
    [hloc : ∀ z : X.carrier, IsLocalRing (ToType (X.presheaf.stalk z))]
    {M N : OXMod.{u, u} X} (x : X.carrier) (hN : FreeAndFiniteStalk N x)
    (ret : Retract ((moduleStalkFunctor X x).obj M) ((moduleStalkFunctor X x).obj N)) :
    FreeAndFiniteStalk M x := by
  have _ := hN.1
  have _ := hN.2
  have h0 : (ret.r.hom).comp (ret.i.hom) = LinearMap.id := by
    rw [← ModuleCat.hom_comp, ret.retract, ModuleCat.hom_id]
  have hsplit : (stalkLinearMapOfHom ret.r).comp (stalkLinearMapOfHom ret.i)
      = LinearMap.id := LinearMap.ext fun m => LinearMap.congr_fun h0 m
  have _ : Module.Flat (ToType (X.presheaf.stalk x))
      (ToType (TopCat.Presheaf.stalk M.val.presheaf x)) :=
    Module.Flat.of_retract _ _ hsplit
  have _ : Module.Finite (ToType (X.presheaf.stalk x))
      (ToType (TopCat.Presheaf.stalk M.val.presheaf x)) :=
    Module.Finite.of_surjective (stalkLinearMapOfHom ret.r) fun m =>
      ⟨stalkLinearMapOfHom ret.i m, congrArg (fun φ => φ m) hsplit⟩
  exact ⟨Module.free_of_flat_of_isLocalRing, inferInstance⟩

/-- At a point of a space with local stalks where all the opcycles of a strictly perfect complex
have finite free stalks, so do all its cohomology sheaves: the cohomology stalk is a direct
summand of the opcycles stalk, hence finite and flat, hence free over the local ring. -/
private theorem freeAndFiniteStalk_homology_of_opcycles
    [hloc : ∀ z : X.carrier, IsLocalRing (ToType (X.presheaf.stalk z))]
    {P : CochainComplex (OXMod.{u, u} X) ℤ} (hP : IsStrictlyPerfect P) (x : X.carrier)
    (hopc : ∀ j : ℤ, FreeAndFiniteStalk (P.opcycles j) x) (i : ℤ) :
    FreeAndFiniteStalk (P.homology i) x := by
  have hXproj : Projective ((stalkComplex P x).X (i + 1)) :=
    projective_moduleStalkFunctor_obj
      (((freeAndFiniteStalk_iff (P.X (i + 1)) x).mp
        (freeAndFiniteStalk_of_isDirectSummandOfFiniteFree (hP.directSummand (i + 1)) x)).1)
  have hOproj : Projective ((stalkComplex P x).opcycles (i + 1)) :=
    Projective.of_iso (stalkComplexOpcyclesIso P x (i + 1)).symm
      (projective_moduleStalkFunctor_obj
        (((freeAndFiniteStalk_iff (P.opcycles (i + 1)) x).mp (hopc (i + 1))).1))
  obtain ⟨ret⟩ := nonempty_retract_homology_opcycles (stalkComplex P x) i hXproj hOproj
  have ret' : Retract ((moduleStalkFunctor X x).obj (P.homology i))
      ((moduleStalkFunctor X x).obj (P.opcycles i)) :=
    (stalkComplexHomologyIso P x i).symm.retract.trans
      (ret.trans (stalkComplexOpcyclesIso P x i).retract)
  exact freeAndFiniteStalk_of_stalkRetract x (hopc i) ret'

/-- At a point of a space with local stalks where all the cohomology sheaves of a strictly
perfect complex have finite free stalks, so do all its opcycles: the opcycles stalk is then
projective, hence a direct summand of the stalk of the term it is a quotient of. -/
private theorem freeAndFiniteStalk_opcycles_of_homology
    [hloc : ∀ z : X.carrier, IsLocalRing (ToType (X.presheaf.stalk z))]
    {P : CochainComplex (OXMod.{u, u} X) ℤ} (hP : IsStrictlyPerfect P) (x : X.carrier)
    (hhom : ∀ i : ℤ, FreeAndFiniteStalk (P.homology i) x) (j : ℤ) :
    FreeAndFiniteStalk (P.opcycles j) x := by
  obtain ⟨b, hb⟩ := hP.bounded.bddAbove
  have hzero : ∀ n : ℤ, b < n → IsZero ((stalkComplex P x).X n) := by
    intro n hn
    refine (moduleStalkFunctor X x).map_isZero ?_
    by_contra hcon
    exact absurd (hb hcon) (by omega)
  have hXproj : ∀ n : ℤ, Projective ((stalkComplex P x).X n) := fun n =>
    projective_moduleStalkFunctor_obj
      (((freeAndFiniteStalk_iff (P.X n) x).mp
        (freeAndFiniteStalk_of_isDirectSummandOfFiniteFree (hP.directSummand n) x)).1)
  have hHproj : ∀ n : ℤ, Projective ((stalkComplex P x).homology n) := fun n =>
    Projective.of_iso (stalkComplexHomologyIso P x n).symm
      (projective_moduleStalkFunctor_obj
        (((freeAndFiniteStalk_iff (P.homology n) x).mp (hhom n)).1))
  have hproj : Projective ((moduleStalkFunctor X x).obj (P.opcycles j)) :=
    Projective.of_iso (stalkComplexOpcyclesIso P x j)
      (projective_opcycles (stalkComplex P x) b hzero hXproj hHproj j)
  have _ : Epi ((moduleStalkFunctor X x).map (P.pOpcycles j)) := inferInstance
  have ret : Retract ((moduleStalkFunctor X x).obj (P.opcycles j))
      ((moduleStalkFunctor X x).obj (P.X j)) :=
    ⟨Projective.factorThru (𝟙 _) ((moduleStalkFunctor X x).map (P.pOpcycles j)),
      (moduleStalkFunctor X x).map (P.pOpcycles j), Projective.factorThru_comp _ _⟩
  exact freeAndFiniteStalk_of_stalkRetract x
    (freeAndFiniteStalk_of_isDirectSummandOfFiniteFree (hP.directSummand j) x) ret

/-- A finite free stalk, read over the `RingCat`-valued stalk ring, is a free module on a
standard finite index set; this is the shape in which [Stacks, Tag 0B8J] takes it. -/
private theorem exists_finsupp_linearEquiv_of_freeAndFiniteStalk (M : OXMod.{u, u} X)
    (x : X.carrier) [Nontrivial (ToType (X.presheaf.stalk x))] (h : FreeAndFiniteStalk M x) :
    ∃ r : ℕ, Nonempty (ToType (TopCat.Presheaf.stalk M.val.presheaf x)
      ≃ₗ[ringCatStalk X x] (ULift.{u} (Fin r) →₀ ringCatStalk X x)) := by
  classical
  obtain ⟨hfree, hfin⟩ := (freeAndFiniteStalk_iff M x).mp h
  have _ := hfree
  have _ := hfin
  have _ : Nontrivial (ringCatStalk X x) := (ringCatStalkEquiv X x).toEquiv.nontrivial
  have b := Module.Free.chooseBasis (ringCatStalk X x)
    (ToType (TopCat.Presheaf.stalk M.val.presheaf x))
  have _ : Finite (Module.Free.ChooseBasisIndex (ringCatStalk X x)
    (ToType (TopCat.Presheaf.stalk M.val.presheaf x))) := Module.Finite.finite_basis b
  have _ : Fintype (Module.Free.ChooseBasisIndex (ringCatStalk X x)
    (ToType (TopCat.Presheaf.stalk M.val.presheaf x))) := Fintype.ofFinite _
  exact ⟨Fintype.card (Module.Free.ChooseBasisIndex (ringCatStalk X x)
      (ToType (TopCat.Presheaf.stalk M.val.presheaf x))),
    ⟨b.repr.trans ((Finsupp.domLCongr (Fintype.equivFin _)).trans
      (Finsupp.domLCongr Equiv.ulift.symm))⟩⟩

/-- A zero module has finite free stalks: they are all zero. -/
private theorem freeAndFiniteStalk_of_isZero {M : OXMod.{u, u} X} (h : IsZero M)
    (x : X.carrier) : FreeAndFiniteStalk M x := by
  have _ : Subsingleton (ToType (TopCat.Presheaf.stalk M.val.presheaf x)) :=
    ModuleCat.subsingleton_of_isZero ((moduleStalkFunctor X x).map_isZero h)
  exact ⟨inferInstance, inferInstance⟩

/-- **Finite freeness of the cohomology stalks of a strictly perfect complex spreads out.** At a
point where all of them are finite free, the opcycles are finite free too, hence free on a
neighbourhood by [Stacks, Tag 0B8J], since they are of finite presentation; on the intersection
of those finitely many neighbourhoods the cohomology stalks are again finite free. -/
private theorem exists_nbhd_freeAndFiniteStalk_homology
    [hloc : ∀ z : X.carrier, IsLocalRing (ToType (X.presheaf.stalk z))]
    {P : CochainComplex (OXMod.{u, u} X) ℤ} (hP : IsStrictlyPerfect P) (x : X.carrier)
    (hx : ∀ i : ℤ, FreeAndFiniteStalk (P.homology i) x) :
    ∃ W : Opens X.carrier, x ∈ W ∧
      ∀ y ∈ W, ∀ i : ℤ, FreeAndFiniteStalk (P.homology i) y := by
  classical
  have hchart : ∀ j : ℤ, ∃ V : Opens X.carrier, x ∈ V ∧ ∃ r : ℕ,
      Nonempty ((P.opcycles j).over V ≅
        _root_.SheafOfModules.free.{u} (ULift.{u} (Fin r))) := by
    intro j
    obtain ⟨r, hr⟩ := exists_finsupp_linearEquiv_of_freeAndFiniteStalk (P.opcycles j) x
      (freeAndFiniteStalk_opcycles_of_homology hP x hx j)
    obtain ⟨V, hxV, he⟩ := Stacks.SheafOfModules.exists_iso_free_over_of_stalk_iso_free
      (P.opcycles j) (Stacks.Cohomology.OpcyclesFinitePresentation.isFinitePresentation_opcycles
        hP j) x r hr
    exact ⟨V, hxV, r, he⟩
  choose V hxV r he using hchart
  set s : Finset ℤ := hP.bounded.toFinset
  refine ⟨⟨⋂ j ∈ s, (V j : Set X.carrier),
    isOpen_biInter_finset fun j _ => (V j).isOpen⟩, ?_, ?_⟩
  · exact Set.mem_iInter₂.mpr fun j _ => hxV j
  · intro y hy i
    refine freeAndFiniteStalk_homology_of_opcycles hP y (fun j => ?_) i
    by_cases hj : IsZero (P.X j)
    · exact freeAndFiniteStalk_of_isZero
        (hj.of_iso ((P.sc j).opcyclesIsoX₂ (hj.eq_of_tgt _ _))) y
    · exact freeAndFiniteStalk_of_overIsoFree (he j).some
        (Set.mem_iInter₂.mp hy j (hP.bounded.mem_toFinset.mpr hj))

/-! ### The two comparisons with the local model -/

/-- **Finite freeness of a stalk is the same before and after restriction to an open set.** The
stalk of the restriction of an `𝒪_X`-module at a point of the open set is the ambient stalk,
semilinearly over the comparison isomorphism `LocallyFreeRank.restrictStalkRingEquiv` of the
stalk rings, and finite freeness transports along that comparison. -/
private theorem freeAndFiniteStalk_restrictModules_iff
    [hloc : ∀ w : X.carrier, IsLocalRing (ToType (X.presheaf.stalk w))]
    (M : OXMod.{u, u} X) (V : Opens X.carrier)
    (z : (X.restrict V.isOpenEmbedding).carrier) :
    FreeAndFiniteStalk ((restrictModules X V).obj M) z ↔ FreeAndFiniteStalk M z.1 := by
  classical
  have hlocS : ∀ w : X.carrier,
      IsLocalRing (ToType (TopCat.Presheaf.stalk X.sheaf.obj w)) := hloc
  let instA : Module (ToType (TopCat.Presheaf.stalk X.sheaf.obj z.1))
      (ToType (TopCat.Presheaf.stalk M.val.presheaf z.1)) :=
    LocallyFreeRank.instModuleStalkF X.carrier X.sheaf M z.1
  let instB : Module (LocallyFreeRank.restrictStalkRing X.carrier X.sheaf z.1 V z.2)
      (ToType (TopCat.Presheaf.stalk M.val.presheaf z.1)) :=
    Module.compHom _
      (LocallyFreeRank.restrictStalkRingEquiv X.carrier X.sheaf z.1 z.2).toRingHom
  let instC := LocallyFreeRank.instModuleStalkRestrictMod X.carrier X.sheaf M z.1 V z.2
  obtain ⟨ea⟩ := LocallyFreeRank.Trivialization.stalk_restrictMod_linearEquiv
    X.carrier X.sheaf M z.1 z.2
  have _ : Nontrivial (ringCatStalk (X.restrict V.isOpenEmbedding) z) :=
    (LocallyFreeRank.restrictStalkRingEquiv X.carrier X.sheaf z.1 z.2).toEquiv.nontrivial
  have _ : Nontrivial (ToType ((X.restrict V.isOpenEmbedding).presheaf.stalk z)) :=
    (ringCatStalkEquiv (X.restrict V.isOpenEmbedding) z).symm.toEquiv.nontrivial
  rw [freeAndFiniteStalk_iff]
  exact freeAndFinite_iff_of_ringEquiv (instMRA := instC) (instMRB := instB)
    (instMSB := instA) (LocallyFreeRank.restrictStalkRingEquiv X.carrier X.sheaf z.1 z.2)
    (fun _ _ => rfl) ea

/-- **The cohomology of a local model computes the restricted cohomology sheaf.** A
quasi-isomorphism from a complex `P` on `X|_V` to the restriction of a complex representing `E`
identifies `H^i(P)` with the restriction of `H^i(E)`, through the exactness of restriction and
the factorisation of the derived cohomology functor. -/
private def localModelHomologyIso [HasDerivedCategory.{d} (OXMod.{u, u} X)]
    {E : DerivedCategory (OXMod.{u, u} X)} {E' : CochainComplex (OXMod.{u, u} X) ℤ}
    (eQ : DerivedCategory.Q.obj E' ≅ E) {V : Opens X.carrier}
    {P : CochainComplex (OXMod.{u, u} (X.restrict V.isOpenEmbedding)) ℤ}
    (f : P ⟶ restrictComplex E' V) [QuasiIso f] (i : ℤ) :
    P.homology i ≅ (restrictModules X V).obj
      ((DerivedCategory.homologyFunctor (OXMod.{u, u} X) i).obj E) :=
  let : PreservesFiniteLimits (restrictModules.{u} X V) :=
    StrictlyPerfect.preservesFiniteLimits_restrictModules V
  let : PreservesFiniteColimits (restrictModules.{u} X V) :=
    StrictlyPerfect.preservesFiniteColimits_restrictModules V
  have : IsIso (HomologicalComplex.homologyMap f i) :=
    (quasiIsoAt_iff_isIso_homologyMap f i).mp (QuasiIso.quasiIsoAt (f := f) i)
  asIso (HomologicalComplex.homologyMap f i) ≪≫
    (E'.sc i).mapHomologyIso (restrictModules X V) ≪≫
    (restrictModules X V).mapIso
      (((DerivedCategory.homologyFunctorFactors (OXMod.{u, u} X) i).app E').symm ≪≫
        (DerivedCategory.homologyFunctor (OXMod.{u, u} X) i).mapIso eQ)

/-! ### Openness -/

/-- **Stacks 0GT1, openness.** On a ringed space whose structure-sheaf stalks are local rings,
the finite free cohomology locus of a perfect object of the derived category of `𝒪_X`-modules is
open: near a point of the locus the object is computed by a strictly perfect complex, whose
opcycles are then free on a neighbourhood, and over such a neighbourhood all the cohomology
stalks are again finite free. -/
@[stacks 0GT1 "openness of the locus"]
theorem isOpen_cohomologyFiniteFreeLocus
    [hloc : ∀ x : X.carrier, IsLocalRing (ToType (X.presheaf.stalk x))]
    [HasDerivedCategory.{d} (OXMod.{u, u} X)] (E : DerivedCategory (OXMod.{u, u} X))
    (hE : IsPerfect E) : IsOpen (cohomologyFiniteFreeLocus E) := by
  rw [isOpen_iff_mem_nhds]
  intro x hx
  obtain ⟨E', hE', ⟨eQ⟩⟩ := hE
  obtain ⟨I, U, hU, hmodels⟩ := hE'
  have hxU : x ∈ iSup U := by
    rw [hU]
    trivial
  obtain ⟨k, hk⟩ := Opens.mem_iSup.mp hxU
  obtain ⟨P, hP, f, hf⟩ := hmodels k
  have _ : QuasiIso f := hf
  have hlocY : ∀ y : (X.restrict (U k).isOpenEmbedding).carrier,
      IsLocalRing (ToType ((X.restrict (U k).isOpenEmbedding).presheaf.stalk y)) := fun y =>
    RingEquiv.isLocalRing
      ((X.restrictStalkIso (U k).isOpenEmbedding y).symm.commRingCatIsoToRingEquiv)
  have hntY : ∀ y : (X.restrict (U k).isOpenEmbedding).carrier,
      Nontrivial (ToType ((X.restrict (U k).isOpenEmbedding).presheaf.stalk y)) := fun y =>
    (hlocY y).toNontrivial
  have hstart : ∀ i : ℤ, FreeAndFiniteStalk (P.homology i) (⟨x, hk⟩ :
      (X.restrict (U k).isOpenEmbedding).carrier) := fun i =>
    freeAndFiniteStalk_of_iso (localModelHomologyIso eQ f i).symm _
      ((freeAndFiniteStalk_restrictModules_iff
        ((DerivedCategory.homologyFunctor (OXMod.{u, u} X) i).obj E) (U k)
        ⟨x, hk⟩).mpr (hx i))
  obtain ⟨W, hxW, hWfree⟩ := exists_nbhd_freeAndFiniteStalk_homology hP ⟨x, hk⟩ hstart
  refine Filter.mem_of_superset
    (((U k).isOpenEmbedding.functor.obj W).isOpen.mem_nhds ⟨⟨x, hk⟩, hxW, rfl⟩) ?_
  rintro _ ⟨z, hzW, rfl⟩ i
  have _ := hntY z
  exact (freeAndFiniteStalk_restrictModules_iff
    ((DerivedCategory.homologyFunctor (OXMod.{u, u} X) i).obj E) (U k) z).mp <|
    freeAndFiniteStalk_of_iso (localModelHomologyIso eQ f i) z (hWfree z hzW i)

end AlgebraicGeometry.RingedSpace

end
