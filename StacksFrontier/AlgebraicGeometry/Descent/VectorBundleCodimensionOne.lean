module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.CoherenceCriteria.Basic
public import StacksFrontier.AlgebraicGeometry.Divisors.AssociatedPoints
public import StacksFrontier.AlgebraicGeometry.Divisors.AssociatedPoints.Depth
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFree.Sheaf
public import StacksFrontier.AlgebraicGeometry.Modules.FiniteLocallyFreeDescent.Fpqc
public import StacksFrontier.AlgebraicGeometry.Modules.FiniteLocallyFreeTFAE
public import StacksFrontier.AlgebraicGeometry.Scheme.FunctorialityQuasiCoherent.Basic
public import StacksFrontier.AlgebraicGeometry.Morphisms.Flat.Module
public import StacksFrontier.AlgebraicGeometry.Properties.Normal
public import StacksFrontier.AlgebraicGeometry.Properties.Serre
public import StacksFrontier.AlgebraicGeometry.PushforwardRegularity.Depth
public import StacksFrontier.AlgebraicGeometry.RingedSpace.Flat
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorStalkRingedSpace
public import StacksFrontier.CategoryTheory.Sites.Modules.Flat
public import StacksFrontier.RingTheory.Depth.FlatLocalHom
public import StacksFrontier.RingTheory.Depth.Nakayama
public import StacksFrontier.Topology.Sheaves.Modules.Flat.Stalk
public import StacksFrontier.Topology.Sheaves.RingedSpace.ModulePullbackStalk

/-!
# Descending a vector bundle along a proper flat family with normal base: the depth argument

Let `f : X ⟶ S` be flat and proper with `𝒪_S = f_*𝒪_X`, let `S` be normal and Noetherian, and
let `ℰ` be a finite locally free `𝒪_X`-module. This file proves that the canonical map
`f^*f_*ℰ → ℰ` is an isomorphism as soon as it is one on stalks over the points of codimension at
most one, and that `ℰ` is then pulled back from a finite locally free `𝒪_S`-module. Over a point
of codimension at least two the source stalk has depth at least two while the point is not
associated to `ℰ`, which is the criterion of Tag 0AVM. The descent statement of Tag 0EXG itself,
which obtains the condition in codimension at most one by flat base change, is
`AlgebraicGeometry.VectorBundleCodimensionOne.exists_isFiniteLocallyFree_pullback_iso` in
`StacksFrontier/AlgebraicGeometry/Descent/VectorBundleCodimensionOne/FreeOverLocalBase.lean`.

## Main results

* `AlgebraicGeometry.VectorBundleCodimensionOne.two_le_depth_stalk_of_isNormal`: on a normal
  locally Noetherian scheme a local ring of dimension at least two has depth at least two.
* `AlgebraicGeometry.VectorBundleCodimensionOne.two_le_depth_stalk_pushforward`: the stalk of
  the pushforward of a module flat over the base inherits depth at least two.
* `AlgebraicGeometry.VectorBundleCodimensionOne.two_le_depth_stalk_pullback`: depth at least
  two passes to the pullback along a flat morphism.
* `AlgebraicGeometry.VectorBundleCodimensionOne.notMem_associatedPoints_of_isFlatOverAt`: a
  point is not associated to a module flat over a base of positive depth.
* `AlgebraicGeometry.VectorBundleCodimensionOne.isFlatOver_of_isFiniteLocallyFree`: a finite
  locally free module on a flat family is flat over the base.
* `AlgebraicGeometry.VectorBundleCodimensionOne.surjective_of_isIso_cMap`: a universally
  closed morphism whose comparison map on structure sheaves is invertible is surjective.
* `exists_isFiniteLocallyFree_pullback_iso_of_isIso_counit` (in the same namespace): an
  invertible counit along a flat surjection exhibits `ℰ` as the pullback of the finite locally
  free module `f_*ℰ`.
* `AlgebraicGeometry.VectorBundleCodimensionOne.isIso_counit_of_isIso_stalk_of_codim_le_one`:
  the counit is an isomorphism once it is one on stalks over the points of codimension at most
  one.

## Implementation notes

The hypothesis `𝒪_S = f_*𝒪_X` is recorded as invertibility of the canonical comparison map
`f.toLRSHom.toHom.c` rather than as an equality of sheaves, and codimension of a point is read
off as the Krull dimension of its local ring. Depth is `Module.depth` along the maximal ideal.

The stalk of a sheaf of modules carries two module structures that are equal but not
syntactically so, one coming from the tensor description of a pullback stalk; the offending
instance is removed locally where the tensor description is the one in play.

The depth estimate needs the stalks of `f_*ℰ` to be finite and `f^*f_*ℰ` to be coherent, which
`isIso_counit_of_isIso_stalk_of_codim_le_one` takes as arguments. Both follow from coherence of
`f_*ℰ`, Tag 02O5, which is proved by dévissage over Chow's lemma; that development is imported
only by `VectorBundleCodimensionOne/FreeOverLocalBase.lean`, because its import cone contributes
a second `HasDerivedCategory` instance that would change the elaboration of the modules importing
this one.

## References

* [Stacks Project, Tag 0EXG](https://stacks.math.columbia.edu/tag/0EXG)
* [Stacks Project, Tag 02O5](https://stacks.math.columbia.edu/tag/02O5)
* [Stacks Project, Tag 0AVM](https://stacks.math.columbia.edu/tag/0AVM)
* [Stacks Project, Tag 0EY0](https://stacks.math.columbia.edu/tag/0EY0)
* [Stacks Project, Tag 0337](https://stacks.math.columbia.edu/tag/0337)
* [Stacks Project, Tag 0345](https://stacks.math.columbia.edu/tag/0345)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.VectorBundleCodimensionOne

/-- On a normal locally Noetherian scheme, a local ring of dimension at least two has depth at
least two: this is the half of Serre's criterion asserting condition `(S₂)`. -/
@[ega "IV 5.8.6" "necessity of clause (ii)", sga "2 XI 3.11" "necessity: (ii)"]
public theorem two_le_depth_stalk_of_isNormal {S : Scheme.{u}} [IsLocallyNoetherian S]
    [IsNormal S] (s : S) (h : (2 : ℕ∞) ≤ ringKrullDim (S.presheaf.stalk s)) :
    (2 : ℕ∞) ≤ Module.depth (S.presheaf.stalk s)
      (IsLocalRing.maximalIdeal (S.presheaf.stalk s)) (S.presheaf.stalk s) := by
  have hs2 :=
    ((isNormal_iff_hasPropertySk_two_and_isRegularInCodimension_one S).mp inferInstance).1 s
  have hs2' : (↑(2 : ℕ∞) : WithBot ℕ∞) ≤
      ↑(Module.depth (S.presheaf.stalk s)
        (IsLocalRing.maximalIdeal (S.presheaf.stalk s)) (S.presheaf.stalk s)) := by
    have hmin : min (↑(2 : ℕ∞) : WithBot ℕ∞) (ringKrullDim (S.presheaf.stalk s)) =
        ↑(2 : ℕ∞) := min_eq_left h
    exact hmin ▸ hs2
  exact WithBot.coe_le_coe.mp hs2'

/-- The stalk of the direct image of a module flat over the base has depth at least two
wherever the base local ring does. -/
public theorem two_le_depth_stalk_pushforward {X S : Scheme.{u}} (f : X ⟶ S) [QuasiCompact f]
    [QuasiSeparated f] (E : X.Modules) [E.IsQuasicoherent]
    (hflat : IsFlatOver f.toLRSHom.toShHom E) (s : S)
    (hdepth : (2 : ℕ∞) ≤ Module.depth (S.presheaf.stalk s)
      (IsLocalRing.maximalIdeal (S.presheaf.stalk s)) (S.presheaf.stalk s))
    (hfinite : Module.Finite (S.presheaf.stalk s) (TopCat.Presheaf.stalk (C := Ab.{u})
      ((Scheme.Modules.pushforward f).obj E).val.presheaf s)) :
    (2 : ℕ∞) ≤ Module.depth (S.presheaf.stalk s)
      (IsLocalRing.maximalIdeal (S.presheaf.stalk s))
      (TopCat.Presheaf.stalk (C := Ab.{u})
        ((Scheme.Modules.pushforward f).obj E).val.presheaf s) := by
  have h := Stacks.AlgebraicGeometry.PushforwardRegularity.min_depth_le_depth_stalk_pushforward
    f E hflat s hfinite
  rwa [min_eq_left hdepth] at h

/-- The stalk of a module pullback is the tensor product of the base stalk with the local ring
of the source. -/
private lemma nonempty_modulePullback_stalk_linearEquiv {X Y : RingedSpace.{u, u}} (f : X ⟶ Y)
    (G : SheafOfModules.{u} (structureSheafRing Y)) (x : X) :
    let G' : PresheafOfModules (Y.presheaf ⋙ forget₂ CommRingCat RingCat) := G.val
    let P' : PresheafOfModules (X.presheaf ⋙ forget₂ CommRingCat RingCat) :=
      ((RingedSpaceModuleAdjunction.modulePullback f).obj G).val
    let _ : Algebra (Y.presheaf.stalk (f.hom.base x)) (X.presheaf.stalk x) :=
      (f.hom.stalkMap x).hom.toAlgebra
    Nonempty (↑(TopCat.Presheaf.stalk P'.presheaf x) ≃ₗ[X.presheaf.stalk x]
      TensorProduct (Y.presheaf.stalk (f.hom.base x)) (X.presheaf.stalk x)
        ↑(TopCat.Presheaf.stalk G'.presheaf (f.hom.base x))) := by
  obtain ⟨e, _⟩ := RingedSpaceModuleAdjunction.exists_modulePullbackStalkLinearEquiv f G x
  exact ⟨e⟩

/-- Depth at least two passes from a module on the base to its pullback along a flat morphism,
by the depth formula for a flat local homomorphism. -/
public theorem two_le_depth_stalk_pullback {X S : Scheme.{u}} (f : X ⟶ S) [Flat f]
    [IsLocallyNoetherian X] [IsLocallyNoetherian S] (F : S.Modules) [F.IsQuasicoherent] (x : X)
    (hdepth : (2 : ℕ∞) ≤ Module.depth (S.presheaf.stalk (f x))
      (IsLocalRing.maximalIdeal (S.presheaf.stalk (f x)))
      (TopCat.Presheaf.stalk (C := Ab.{u}) F.val.presheaf (f x)))
    (hfinite : Module.Finite (S.presheaf.stalk (f x))
      (TopCat.Presheaf.stalk (C := Ab.{u}) F.val.presheaf (f x))) :
    (2 : ℕ∞) ≤ Module.depth (X.presheaf.stalk x)
      (IsLocalRing.maximalIdeal (X.presheaf.stalk x))
      (TopCat.Presheaf.stalk (C := Ab.{u})
        ((Scheme.Modules.pullback f).obj F).val.presheaf x) := by
  let A := S.presheaf.stalk (f x)
  let B := X.presheaf.stalk x
  let M := TopCat.Presheaf.stalk (C := Ab.{u}) F.val.presheaf (f x)
  let _ : Algebra A B := (f.stalkMap x).hom.toAlgebra
  let _ : IsNoetherianRing A := inferInstance
  let _ : IsNoetherianRing B := inferInstance
  let _ : IsLocalHom (algebraMap A B) := by
    rw [RingHom.algebraMap_toAlgebra]
    infer_instance
  let _ : Module.Flat A B := Flat.stalkMap f x
  let _ : Module.Finite A M := hfinite
  have hformula := Module.depth_tensorProduct_of_flat (R := A) (S := B) (M := M) (N := B)
  obtain ⟨e⟩ := nonempty_modulePullback_stalk_linearEquiv f.toLRSHom.toShHom F x
  have hdepthEq : Module.depth B (IsLocalRing.maximalIdeal B)
      (TopCat.Presheaf.stalk (C := Ab.{u})
        ((Scheme.Modules.pullback f).obj F).val.presheaf x) =
      Module.depth B (IsLocalRing.maximalIdeal B) (TensorProduct A B M) :=
    Module.depth_eq_depth_of_linearEquiv (IsLocalRing.maximalIdeal B) e
  have hfiber : 0 ≤ Module.depth B (IsLocalRing.maximalIdeal B)
      (B ⧸ ((IsLocalRing.maximalIdeal A).map (algebraMap A B) • (⊤ : Submodule B B))) := by
    positivity
  rw [hdepthEq, hformula]
  exact le_trans hdepth (le_add_of_nonneg_right hfiber)

/-- A point is not associated to a module that is flat over the base at that point, provided
the base local ring below it has positive depth. -/
public theorem notMem_associatedPoints_of_isFlatOverAt {X S : Scheme.{u}} (f : X ⟶ S) [Flat f]
    (E : X.Modules) (x : X)
    (hdepth : (1 : ℕ∞) ≤ Module.depth (S.presheaf.stalk (f x))
      (IsLocalRing.maximalIdeal (S.presheaf.stalk (f x))) (S.presheaf.stalk (f x)))
    (hflat : IsFlatOverAt f.toLRSHom.toShHom E x) :
    x ∉ Stacks.Divisors.associatedPoints E := by
  let A := S.presheaf.stalk (f x)
  let B := X.presheaf.stalk x
  let N := TopCat.Presheaf.stalk (C := Ab.{u}) E.val.presheaf x
  let ρ := (f.stalkMap x).hom
  let _ : Module B N :=
    PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
      (R := X.presheaf) E.val x
  let _ : Module A N := Module.compHom N ρ
  change Module.Flat A N at hflat
  let _ : Module.Flat A N := hflat
  have hrdepth : 1 ≤ Module.depth A (IsLocalRing.maximalIdeal A) A := hdepth
  obtain ⟨r, hr, hreg⟩ :=
    (Module.one_le_depth_iff_exists_isSMulRegular (R := A) (M := A)
      (IsLocalRing.maximalIdeal A)).mp hrdepth
  have hrnd : r ∈ nonZeroDivisors A := by
    rw [mem_nonZeroDivisors_iff]
    refine ⟨fun a ha => hreg.right_eq_zero_of_smul (by simpa [smul_eq_mul] using ha),
      fun a ha => hreg.right_eq_zero_of_smul (by simpa [smul_eq_mul, mul_comm] using ha)⟩
  have hregN : IsSMulRegular N r := Module.Flat.isSMulRegular_of_nonZeroDivisors hrnd
  let _ : IsLocalHom ρ := f.toLRSHom.prop x
  intro hass
  change IsAssociatedPrimeStacks B N (IsLocalRing.maximalIdeal B) at hass
  obtain ⟨_, m, hm⟩ := hass
  have hrB : ρ r ∈ IsLocalRing.maximalIdeal B := map_nonunit ρ r hr
  have hcolon : ρ r ∈ (⊥ : Submodule B N).colon (Submodule.span B {m}) := by
    rw [hm]; exact hrB
  have hkillB : ρ r • m = 0 := by
    simpa using (Submodule.mem_colon.mp hcolon) m (Submodule.subset_span rfl)
  have hm0 : m = 0 := hregN.right_eq_zero_of_smul (show ρ r • m = 0 from hkillB)
  have hmaxTop : IsLocalRing.maximalIdeal B = ⊤ := by
    calc IsLocalRing.maximalIdeal B = (⊥ : Submodule B N).colon (Submodule.span B {m}) := hm.symm
      _ = ⊤ := by simp [hm0]
  exact (IsLocalRing.maximalIdeal.isMaximal B).ne_top hmaxTop

/-- A finite locally free module on a scheme flat over a base is flat over that base. -/
public theorem isFlatOver_of_isFiniteLocallyFree {X S : Scheme.{u}} (f : X ⟶ S) [Flat f]
    (E : X.Modules) [E.IsQuasicoherent]
    [SheafOfModules.IsFiniteLocallyFree.{u, u, u} E] :
    IsFlatOver f.toLRSHom.toShHom E := by
  have hpair : SheafOfModules.IsFlat (C := TopologicalSpace.Opens X.toTopCat)
      (J := Opens.grothendieckTopology X.toTopCat) (O := X.sheaf) E ∧
      E.IsFinitePresentation :=
    ((Stacks.FiniteLocallyFree.ModuleTFAE.finiteLocallyFree_tfae E).out 4 1).mp
      (inferInstance : SheafOfModules.IsFiniteLocallyFree.{u, u, u} E)
  intro x
  let R := X.toRingedSpace.presheaf.stalk x
  let N := TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) E.val.presheaf x
  let _ : Module R N :=
    PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier E.val x
  have hEflatAt := (SheafOfModules.isFlat_iff_stalk_flat X.sheaf E).mp hpair.1 x
  have hId : IsFlatOverAt (𝟙 X.toRingedSpace) E x := by
    change @Module.Flat R N _ _
      (Module.compHom N (PresheafedSpace.Hom.stalkMap
        (𝟙 X.toRingedSpace.toPresheafedSpace) x).hom)
    have hmod : (Module.compHom N (RingHom.id R) : Module R N) =
        (inferInstance : Module R N) := by
      apply Module.ext
      funext r n
      rfl
    have hmap : (PresheafedSpace.Hom.stalkMap
        (𝟙 X.toRingedSpace.toPresheafedSpace) x).hom = RingHom.id R := by
      change ((𝟙 X : X ⟶ X).stalkMap x).hom = _
      exact congrArg CommRingCat.Hom.hom (Scheme.Hom.stalkMap_id X x)
    rw [hmap, hmod]
    exact hEflatAt
  have hf : IsFlatAt f.toLRSHom.toShHom x := (Flat.iff_flat_stalkMap f).mp inferInstance x
  have hcomp := IsFlatOverAt.comp (𝟙 X.toRingedSpace) f.toLRSHom.toShHom E x hId hf
  change IsFlatOverAt f.toLRSHom.toShHom E x
  simpa using hcomp

/-- A universally closed morphism whose comparison map `𝒪_S ⟶ f_*𝒪_X` is invertible is
surjective: over a point outside the image the target sections vanish, forcing `1 = 0` in the
local ring there. -/
public theorem surjective_of_isIso_cMap {X S : Scheme.{u}} (f : X ⟶ S) [UniversallyClosed f]
    (hO : IsIso f.toLRSHom.toHom.c) : Surjective f := by
  constructor
  intro s
  by_contra hs
  have hclosed : IsClosed (Set.range f) := f.isClosedMap.isClosed_range
  let U : S.Opens := ⟨(Set.range f)ᶜ, hclosed.isOpen_compl⟩
  have hsU : s ∈ U := by simpa [U] using hs
  have hpre : f ⁻¹ᵁ U = ⊥ := by
    ext x
    change f x ∈ (Set.range f)ᶜ ↔ x ∈ (∅ : Set X)
    simp
  have hOXterm : IsTerminal (X.toRingedSpace.sheaf.obj.obj (op (⊥ : X.Opens))) :=
    X.toRingedSpace.sheaf.isTerminalOfEmpty
  have htarget : Subsingleton (((Scheme.Modules.pushforward f).obj
      (SheafOfModules.unit X.ringCatSheaf)).val.presheaf.obj (op U)) := by
    change Subsingleton (X.toRingedSpace.presheaf.obj
      (op ((TopologicalSpace.Opens.map f.toLRSHom.toHom.base).obj U)))
    rw [show (TopologicalSpace.Opens.map f.toLRSHom.toHom.base).obj U = ⊥ from hpre]
    exact CommRingCat.subsingleton_of_isTerminal hOXterm
  have hsource : Subsingleton (S.toRingedSpace.presheaf.obj (op U)) := by
    refine ⟨fun a b => ?_⟩
    have hab : (f.toLRSHom.toHom.c.app (op U)) a = (f.toLRSHom.toHom.c.app (op U)) b :=
      htarget.elim _ _
    exact ((ConcreteCategory.isIso_iff_bijective _).mp
      (NatIso.isIso_app_of_isIso f.toLRSHom.toHom.c (op U))).1 hab
  have h01 : (1 : S.toRingedSpace.presheaf.obj (op U)) = 0 := hsource.elim _ _
  have h := congrArg (fun a => (S.presheaf.germ U s hsU).hom a) h01
  simp at h

/-- A flat, quasi-compact, quasi-separated surjection along which the counit `f^*f_*ℰ ⟶ ℰ` is
invertible exhibits `ℰ` as the pullback of the finite locally free module `f_*ℰ`: the single
morphism `f` is an fpqc covering, and finite local freeness descends along it. -/
public theorem exists_isFiniteLocallyFree_pullback_iso_of_isIso_counit {X S : Scheme.{u}}
    (f : X ⟶ S) [Flat f] [QuasiCompact f] [QuasiSeparated f] [Surjective f] (E : X.Modules)
    [SheafOfModules.IsFiniteLocallyFree.{u, u, u} E]
    (hε : IsIso ((Scheme.Modules.pullbackPushforwardAdjunction f).counit.app E)) :
    ∃ M : S.Modules, SheafOfModules.IsFiniteLocallyFree.{u, u, u} M ∧
      Nonempty ((Scheme.Modules.pullback f).obj M ≅ E) := by
  let _ : E.IsQuasicoherent :=
    Stacks.AlgebraicGeometry.CoherenceCriteria.isQuasicoherent_of_isFiniteLocallyFree E
  let M := (Scheme.Modules.pushforward f).obj E
  let ε := (Scheme.Modules.pullbackPushforwardAdjunction f).counit.app E
  let 𝒰 : S.Cover.{u} Scheme.fpqcPrecoverage :=
    { __ := PreZeroHypercover.singleton f
      mem₀ := by
        rw [PreZeroHypercover.presieve₀_singleton, Scheme.fpqcPrecoverage]
        exact Scheme.Hom.singleton_mem_propQCPrecoverage inferInstance }
  have hcover : ∀ i, SheafOfModules.IsFiniteLocallyFree.{u, u, u}
      ((Scheme.Modules.pullback (𝒰.f i)).obj M) := by
    intro i
    cases i
    dsimp [𝒰]
    exact SheafOfModules.IsFiniteLocallyFree.of_iso (asIso ε).symm
      (h := inferInstanceAs (SheafOfModules.IsFiniteLocallyFree.{u, u, u} E))
  refine ⟨M, isFiniteLocallyFree_of_pullback_fpqcCover M 𝒰 hcover, ⟨?_⟩⟩
  simpa [M] using asIso ε

/-- The counit `f^*f_*ℰ ⟶ ℰ` of a flat family over a normal Noetherian base is an isomorphism
as soon as it is an isomorphism on stalks over the points of codimension at most one. Over a
point of codimension at least two the source stalk has depth at least two, by Serre's condition
`(S₂)` on the base together with the depth bounds for a flat pushforward and for a flat base
change, and the point is not associated to `ℰ`; this is the criterion of Tag 0AVM. -/
public theorem isIso_counit_of_isIso_stalk_of_codim_le_one {X S : Scheme.{u}} (f : X ⟶ S)
    [Flat f] [QuasiCompact f] [QuasiSeparated f] [IsLocallyNoetherian X]
    [IsLocallyNoetherian S] [IsNormal S] (E : X.Modules) [E.IsQuasicoherent]
    [SheafOfModules.IsFiniteLocallyFree.{u, u, u} E]
    [((Scheme.Modules.pushforward f ⋙ Scheme.Modules.pullback f).obj E).IsCoherent]
    [((Scheme.Modules.pushforward f ⋙ Scheme.Modules.pullback f).obj E).IsQuasicoherent]
    [((𝟭 X.Modules).obj E).IsQuasicoherent]
    (hstalkFinite : ∀ s : S, Module.Finite (S.presheaf.stalk s)
      (TopCat.Presheaf.stalk (C := Ab.{u})
        ((Scheme.Modules.pushforward f).obj E).val.presheaf s))
    (hcodim : ∀ x : X, ringKrullDim (S.presheaf.stalk (f x)) ≤ 1 →
      IsIso ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
        ((PresheafOfModules.toPresheaf X.ringCatSheaf.obj).map
          ((Scheme.Modules.pullbackPushforwardAdjunction f).counit.app E).val))) :
    IsIso ((Scheme.Modules.pullbackPushforwardAdjunction f).counit.app E) := by
  have hflat : IsFlatOver f.toLRSHom.toShHom E := isFlatOver_of_isFiniteLocallyFree f E
  let _ : ((Scheme.Modules.pushforward f).obj E).IsQuasicoherent :=
    AlgebraicGeometry.pushforward_isQuasicoherent f E
  apply isIso_of_stalk_isIso_or_depth_two_and_not_associated
    ((Scheme.Modules.pullbackPushforwardAdjunction f).counit.app E)
  intro x
  by_cases hdim : ringKrullDim (S.presheaf.stalk (f x)) ≤ 1
  · exact Or.inl (hcodim x hdim)
  · have hdim2 : (2 : ℕ∞) ≤ ringKrullDim (S.presheaf.stalk (f x)) := by
      change (1 + 1 : WithBot ℕ∞) ≤ ringKrullDim (S.presheaf.stalk (f x))
      exact ENat.WithBot.add_one_le_iff.mpr (lt_of_not_ge hdim)
    have hbase := two_le_depth_stalk_of_isNormal (f x) hdim2
    refine Or.inr ⟨?_, ?_⟩
    · exact two_le_depth_stalk_pullback f ((Scheme.Modules.pushforward f).obj E) x
        (two_le_depth_stalk_pushforward f E hflat (f x) hbase (hstalkFinite (f x)))
        (hstalkFinite (f x))
    · exact notMem_associatedPoints_of_isFlatOverAt f E x
        (le_trans (by norm_num) hbase) (hflat x)

end AlgebraicGeometry.VectorBundleCodimensionOne

end
