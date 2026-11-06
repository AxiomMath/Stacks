module

public import StacksFrontier.Deformation.SquareZero.AlgebraExtensionMaps
public import Mathlib.Algebra.Module.TransferInstance

/-!
# Solutions of a square-zero extension problem as a fibre (Stacks 0GPX)

Let `0 → I → A' → A → 0` be a square-zero extension of commutative rings, let `A → B` be a
ring map, let `N` be a `B`-module and let `c : I → N` be `A`-linear, as in **Stacks 08S4**.
The thickening `A'` is itself a square-zero extension of the `A'`-algebra `A` by `I`, so
**Stacks 0GPT** attaches to it a canonical class `ξ ∈ Ext¹_A(NL_{A/A'}, I)`.

This file proves that the set of isomorphism classes of solutions of the extension problem is
canonically bijective to the fibre of
`Ext¹_B(NL_{B/A'}, N) → Ext¹_A(NL_{A/A'}, N)` over the image of `ξ` under the map
`Ext¹_A(NL_{A/A'}, I) → Ext¹_A(NL_{A/A'}, N)` induced by `c`.

## Main definitions

* `Stacks.Deformation.baseExtension`: the thickening `A'`, viewed as a square-zero extension
  of the `A'`-algebra `A` by `I`.
* `Stacks.Deformation.baseExtClass`: the canonical class `ξ` of that extension.
* `Stacks.Deformation.forgetMapOnIdeal`: a solution of the extension problem, viewed as a
  square-zero extension of the `A'`-algebra `B` by `N` by forgetting `c`.
* `Stacks.Deformation.solutionExtClass`: the class in `Ext¹_B(NL_{B/A'}, N)` of the
  underlying extension of a solution.
* `Stacks.Deformation.solutionsFibre`: the fibre over the image of `ξ`.
* `Stacks.Deformation.solutionsEquivFibre`: **Stacks 0GPX**, the canonical bijection.

## Main results

* `Stacks.Deformation.towerMap_eq_iff_mapOnIdeal`: the key step. An extension of the
  `A'`-algebra `B` by `N` has its class in the fibre over the image of `ξ` exactly when its
  identification of the kernel with `N` carries `c` to the map induced by `A' → B'`, i.e.
  exactly when it is a solution of the extension problem.
* `Stacks.Deformation.solutionsEquivFibre_apply`: the bijection sends the class of a solution
  to the class of its underlying square-zero extension of the `A'`-algebra `B` by `N`.

## Implementation notes

**Stacks 0GPT** confines the middle ring of a square-zero extension of `B` by `N` to the
universe `max uB uN`.  Applying it to `A' → A` and the `A`-module `I` therefore needs `A'`
presented in universe `max u₁ u₂`, so `baseExtension` uses `ULift A'`; the canonical
`A`-module structure on `I` is transported to the kernel of `ULift A' → A` along the evident
additive equivalence.

The whole content is extracted from **Stacks 0GPV** applied to `A' → A → B` and `c : I → N`,
together with the observation that an `A'`-algebra map out of `ULift A'` is unique.  Hence
the auxiliary compatible map whose existence 0GPV characterises is forced to be
`algebraMap A' B'`, and its compatibility with `c` is literally the `map_I` field of a
solution.  The bijection is therefore built by `Equiv.ofBijective` from the honest forward
map "class of a solution ↦ class of its underlying extension", whose value is recorded by
`solutionsEquivFibre_apply`; no choice enters the forward direction.

## References

* [Stacks Project, Tag 0GPX](https://stacks.math.columbia.edu/tag/0GPX)
-/

@[expose] public noncomputable section

universe u₁ u₂ u₃ u₄

open CategoryTheory

namespace Stacks.Deformation

variable (S : SquareZeroExtensionProblem.{u₁, u₂, u₃, u₄})

/-- The thickening `A'`, lifted to the universe in which **Stacks 0GPT** places the middle
ring of a square-zero extension of `A` by `I`. -/
public abbrev thickenedBase := ULift.{u₂} S.A'

/-- The reduction `A' → A` of the given square-zero extension, as an `A'`-algebra map out of
the universe-lifted thickening. -/
public def baseReduction : thickenedBase S →ₐ[S.A'] S.A :=
  (Algebra.ofId S.A' S.A).comp (ULift.algEquiv (R := S.A') (A := S.A')).toAlgHom

/-- An element of the lifted thickening lies in the kernel of `baseReduction` exactly when it
lies in the ideal `I`. -/
public theorem mem_ker_baseReduction {x : thickenedBase S} :
    x ∈ RingHom.ker (baseReduction S).toRingHom ↔ x.down ∈ S.I := by
  rw [RingHom.mem_ker, ← S.kernel_eq, RingHom.mem_ker]
  rfl

/-- The kernel of `baseReduction` is additively the ideal `I`. -/
public def kernelAddEquiv : (RingHom.ker (baseReduction S).toRingHom) ≃+ S.I where
  toFun x := ⟨x.1.down, (mem_ker_baseReduction S).1 x.2⟩
  invFun i := ⟨ULift.up i.1, (mem_ker_baseReduction S).2 i.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl

/-- The thickening `A'` itself, viewed as a square-zero extension of the `A'`-algebra `A` by
the ideal `I`.  Its middle ring is `ULift A'`, its reduction is the given `A' → A`, and its
kernel is identified with `I` by the evident map. -/
public def baseExtension :
    (algebraExtensionProblem S.A' S.A S.I).CompatibleExtension.{max u₂ u₁} := by
  let : Module S.A (RingHom.ker (baseReduction S).toRingHom) := (kernelAddEquiv S).module S.A
  dsimp only [algebraExtensionProblem]
  exact
    { B' := thickenedBase S
      toB := baseReduction S
      surjective a := (S.surjective a).elim fun a' ha' ↦ ⟨⟨a'⟩, ha'⟩
      sq_zero := by
        rw [pow_two]
        refine le_antisymm (Ideal.mul_le.2 fun r hr s hs ↦ ?_) bot_le
        have h : r.down * s.down ∈ S.I ^ 2 := pow_two S.I ▸
          Ideal.mul_mem_mul ((mem_ker_baseReduction S).1 hr) ((mem_ker_baseReduction S).1 hs)
        rw [S.sq_zero] at h
        exact Ideal.mem_bot.2 (ULift.ext (by simpa using h))
      toB_smul_kernel := by
        intro b' x
        apply (kernelAddEquiv S).injective
        have h1 : kernelAddEquiv S (baseReduction S b' • x) =
            baseReduction S b' • kernelAddEquiv S x :=
          ((kernelAddEquiv S).linearEquiv S.A).map_smul _ _
        have h2 : kernelAddEquiv S (b' • x) = b'.down • kernelAddEquiv S x := Subtype.ext rfl
        rw [h1, h2]
        exact S.algebraMap_smul_I b'.down (kernelAddEquiv S x)
      kernelEquiv := ((kernelAddEquiv S).linearEquiv S.A).symm
      map_I i := by
        obtain rfl : i = 0 := Subtype.ext i.2
        simp only [map_zero, Submodule.coe_zero] }

/-- The canonical class `ξ ∈ Ext¹_A(NL_{A/A'}, I)` of the square-zero thickening `A'`: the
value of the classification of **Stacks 0GPT** on `baseExtension`. -/
@[stacks 0GPX "the class ξ of the thickening A', via Lemma 0GPT"]
public def baseExtClass : naiveCotangentExtOne S.A' S.A S.I :=
  squareZeroAlgebraExtensionClassesEquivExtOne S.A' S.A S.I
    (Quotient.mk (SquareZeroExtensionProblem.CompatibleExtension.isomorphicSetoid
      (algebraExtensionProblem S.A' S.A S.I)) (baseExtension S))

/-- The canonical class of the thickening is the obstruction class of **Stacks 08S5**
comparing the split extension `A ⋉ I` with `A'`. -/
public theorem baseExtClass_eq_obstructionClass :
    baseExtClass S =
      (obstructionClass (comparisonDiagram (splitAlgebraExtension S.A' S.A S.I)
        (baseExtension S))).1 := by
  have h := squareZeroAlgebraExtensionClassesEquivExtOne_sub S.A' S.A S.I
    (splitAlgebraExtension S.A' S.A S.I) (baseExtension S)
  rwa [squareZeroAlgebraExtensionClassesEquivExtOne_split_eq_zero, sub_zero] at h

/-- The canonical `A'`-algebra map from the lifted thickening into any `A'`-algebra: an
`A'`-algebra map out of `ULift A'` is unique, since `ULift A'` is generated by the image of
`A'`. -/
public def thickenedBaseHom (T : Type*) [CommRing T] [Algebra S.A' T] :
    thickenedBase S →ₐ[S.A'] T :=
  (Algebra.ofId S.A' T).comp (ULift.algEquiv (R := S.A') (A := S.A')).toAlgHom

/-- `thickenedBaseHom S T` sends `z` to the image of `z.down` under the structure map. -/
public lemma thickenedBaseHom_apply (T : Type*) [CommRing T] [Algebra S.A' T]
    (z : thickenedBase S) : thickenedBaseHom S T z = algebraMap S.A' T z.down := rfl

/-- Any `A'`-algebra map out of the lifted thickening is the canonical one. -/
public lemma algHom_thickenedBase_eq (T : Type*) [CommRing T] [Algebra S.A' T]
    (f : thickenedBase S →ₐ[S.A'] T) : f = thickenedBaseHom S T := by
  ext z
  have h : z = algebraMap S.A' (thickenedBase S) z.down := rfl
  rw [h, AlgHom.commutes, thickenedBaseHom_apply, h]
  exact (AlgHom.commutes (thickenedBaseHom S T) z.down).symm

/-- A solution of the extension problem, viewed as a square-zero extension of the
`A'`-algebra `B` by `N` by forgetting the prescribed map `c` on ideals. -/
public def forgetMapOnIdeal (P : S.CompatibleExtension.{max u₃ u₄}) :
    (algebraExtensionProblem S.A' S.B S.N).CompatibleExtension.{max u₃ u₄} := by
  dsimp only [algebraExtensionProblem]
  exact
    { B' := P.B'
      commRingB' := P.commRingB'
      algebraA'B' := P.algebraA'B'
      toB := P.toB
      surjective := P.surjective
      sq_zero := P.sq_zero
      moduleKernel := P.moduleKernel
      toB_smul_kernel := P.toB_smul_kernel
      kernelEquiv := P.kernelEquiv
      map_I i := by
        obtain rfl : i = 0 := Subtype.ext i.2
        simp only [map_zero, Submodule.coe_zero] }

/-- The class in `Ext¹_B(NL_{B/A'}, N)` of the square-zero extension of the `A'`-algebra `B`
by `N` underlying a solution of the extension problem. -/
public def solutionExtClass (P : S.CompatibleExtension.{max u₃ u₄}) :
    naiveCotangentExtOne S.A' S.B S.N :=
  squareZeroAlgebraExtensionClassesEquivExtOne S.A' S.B S.N
    (Quotient.mk (SquareZeroExtensionProblem.CompatibleExtension.isomorphicSetoid
      (algebraExtensionProblem S.A' S.B S.N)) (forgetMapOnIdeal S P))

/-- **The key step.**  A square-zero extension `0 → N → B' → B → 0` of `A'`-algebras has its
class in the fibre of `Ext¹_B(NL_{B/A'}, N) → Ext¹_A(NL_{A/A'}, N)` over the image of `ξ`
exactly when the map `A' → B'` induces the prescribed map `c : I → N` on ideals, that is,
exactly when `B'` is a solution of the extension problem.

The right-to-left direction is **Stacks 0GPV** applied to `A' → A → B`; the left-to-right
direction uses in addition that an `A'`-algebra map out of `ULift A'` is unique, so that the
map `A' → B'` whose existence 0GPV provides is the structural one. -/
public theorem towerMap_eq_iff_mapOnIdeal
    (Y : (algebraExtensionProblem S.A' S.B S.N).CompatibleExtension.{max u₃ u₄}) :
    naiveCotangentExtOneTowerMap S.A' S.A S.B
        (squareZeroAlgebraExtensionClassesEquivExtOne S.A' S.B S.N
          (Quotient.mk (SquareZeroExtensionProblem.CompatibleExtension.isomorphicSetoid
            (algebraExtensionProblem S.A' S.B S.N)) Y))
      = naiveCotangentExtOneMap S.A' S.A S.c (baseExtClass S) ↔
      ∀ i : S.I, kernelInclusion Y (S.c i) = algebraMap S.A' Y.B' i := by
  rw [baseExtClass, eq_comm,
    ← exists_compatible_algebraMap_iff S.A' S.A S.B S.c (baseExtension S) Y]
  constructor
  · rintro ⟨f, -, hf⟩ i
    rw [← hf i, algHom_thickenedBase_eq S Y.B' f]
    rfl
  · refine fun hmap ↦ ⟨thickenedBaseHom S Y.B', fun z ↦ ?_, fun i ↦ ?_⟩
    · exact (Y.toB.commutes z.down).trans (IsScalarTower.algebraMap_apply S.A' S.A S.B z.down)
    · exact ((hmap i).trans (thickenedBaseHom_apply S Y.B' (ULift.up i.1)).symm).symm

/-- A square-zero extension of the `A'`-algebra `B` by `N` whose structure map `A' → B'`
induces the prescribed map `c` on ideals is a solution of the extension problem. -/
public def ofMapOnIdeal
    (Y : (algebraExtensionProblem S.A' S.B S.N).CompatibleExtension.{max u₃ u₄})
    (hmap : ∀ i : S.I, kernelInclusion Y (S.c i) = algebraMap S.A' Y.B' i) :
    S.CompatibleExtension.{max u₃ u₄} where
  B' := Y.B'
  commRingB' := Y.commRingB'
  algebraA'B' := Y.algebraA'B'
  toB := Y.toB
  surjective := Y.surjective
  sq_zero := Y.sq_zero
  moduleKernel := Y.moduleKernel
  toB_smul_kernel := Y.toB_smul_kernel
  kernelEquiv := Y.kernelEquiv
  map_I := hmap

/-- Forgetting the condition on ideals undoes `ofMapOnIdeal`. -/
public lemma forgetMapOnIdeal_ofMapOnIdeal
    (Y : (algebraExtensionProblem S.A' S.B S.N).CompatibleExtension.{max u₃ u₄})
    (hmap : ∀ i : S.I, kernelInclusion Y (S.c i) = algebraMap S.A' Y.B' i) :
    forgetMapOnIdeal S (ofMapOnIdeal S Y hmap) = Y := rfl

/-- An isomorphism of solutions of the extension problem is in particular an isomorphism of
the underlying square-zero extensions of the `A'`-algebra `B` by `N`. -/
public def isoForgetMapOnIdeal {X Y : S.CompatibleExtension.{max u₃ u₄}}
    (e : SquareZeroExtensionProblem.CompatibleExtension.Iso X Y) :
    SquareZeroExtensionProblem.CompatibleExtension.Iso
      (forgetMapOnIdeal S X) (forgetMapOnIdeal S Y) where
  toAlgEquiv := e.toAlgEquiv
  toB_comm := e.toB_comm
  kernelEquiv_comm := e.kernelEquiv_comm

/-- Conversely, an isomorphism of the underlying extensions of two solutions is an
isomorphism of solutions: the defining conditions are the same. -/
public def isoOfForgetMapOnIdeal {X Y : S.CompatibleExtension.{max u₃ u₄}}
    (e : SquareZeroExtensionProblem.CompatibleExtension.Iso
      (forgetMapOnIdeal S X) (forgetMapOnIdeal S Y)) :
    SquareZeroExtensionProblem.CompatibleExtension.Iso X Y where
  toAlgEquiv := e.toAlgEquiv
  toB_comm := e.toB_comm
  kernelEquiv_comm := e.kernelEquiv_comm

/-- The class of the underlying extension only depends on the isomorphism class of the
solution. -/
public lemma solutionExtClass_eq_of_iso {X Y : S.CompatibleExtension.{max u₃ u₄}}
    (e : SquareZeroExtensionProblem.CompatibleExtension.Iso X Y) :
    solutionExtClass S X = solutionExtClass S Y :=
  congrArg (squareZeroAlgebraExtensionClassesEquivExtOne S.A' S.B S.N)
    (Quotient.sound ⟨isoForgetMapOnIdeal S e⟩)

/-- The class of the underlying extension of a solution lies in the fibre over the image of
`ξ`: this is the half of the key step supplied by the solution's own compatibility with `c`. -/
public lemma towerMap_solutionExtClass (P : S.CompatibleExtension.{max u₃ u₄}) :
    naiveCotangentExtOneTowerMap S.A' S.A S.B (solutionExtClass S P)
      = naiveCotangentExtOneMap S.A' S.A S.c (baseExtClass S) :=
  (towerMap_eq_iff_mapOnIdeal S (forgetMapOnIdeal S P)).mpr fun i ↦ P.map_I i

/-- The fibre of `Ext¹_B(NL_{B/A'}, N) → Ext¹_A(NL_{A/A'}, N)` over the image of the canonical
class `ξ` of the thickening `A'` under the map `Ext¹_A(NL_{A/A'}, I) → Ext¹_A(NL_{A/A'}, N)`
induced by `c : I → N`. -/
@[stacks 0GPX "the fibre over the image of the class of the thickening"]
public abbrev solutionsFibre :=
  {ζ : naiveCotangentExtOne S.A' S.B S.N //
    naiveCotangentExtOneTowerMap S.A' S.A S.B ζ
      = naiveCotangentExtOneMap S.A' S.A S.c (baseExtClass S)}

/-- The canonical map from isomorphism classes of solutions to the fibre: a solution goes to
the class of its underlying square-zero extension of the `A'`-algebra `B` by `N`. -/
public def solutionClassMap :
    SquareZeroExtensionProblem.CompatibleExtension.IsomorphismClasses.{u₁, u₂, u₃, u₄,
      max u₃ u₄} S → solutionsFibre S :=
  Quotient.lift (fun P ↦ (⟨solutionExtClass S P, towerMap_solutionExtClass S P⟩ :
      solutionsFibre S))
    fun _ _ ⟨e⟩ ↦ Subtype.ext (solutionExtClass_eq_of_iso S e)

/-- `solutionClassMap S` sends the class of a solution to the class of its underlying
extension. -/
public lemma solutionClassMap_mk (P : S.CompatibleExtension.{max u₃ u₄}) :
    (solutionClassMap S (Quotient.mk
      (SquareZeroExtensionProblem.CompatibleExtension.isomorphicSetoid S) P)).1
      = solutionExtClass S P := rfl

/-- Two solutions whose underlying extensions have the same class are isomorphic. -/
public lemma solutionClassMap_injective : Function.Injective (solutionClassMap S) := by
  refine fun q₁ q₂ ↦ Quotient.inductionOn₂ q₁ q₂ (fun X Y h ↦ ?_)
  have h' : solutionExtClass S X = solutionExtClass S Y := congrArg Subtype.val h
  have h₂ : (Quotient.mk (SquareZeroExtensionProblem.CompatibleExtension.isomorphicSetoid
      (algebraExtensionProblem S.A' S.B S.N)) (forgetMapOnIdeal S X))
      = Quotient.mk _ (forgetMapOnIdeal S Y) :=
    (squareZeroAlgebraExtensionClassesEquivExtOne S.A' S.B S.N).injective h'
  obtain ⟨e⟩ := Quotient.exact h₂
  exact Quotient.sound ⟨isoOfForgetMapOnIdeal S e⟩

/-- Every class in the fibre is the class of a solution. -/
public lemma solutionClassMap_surjective : Function.Surjective (solutionClassMap S) := by
  rintro ⟨ζ, hζ⟩
  obtain ⟨q, hq⟩ := (squareZeroAlgebraExtensionClassesEquivExtOne S.A' S.B S.N).surjective ζ
  obtain ⟨Y, hY⟩ := Quotient.exists_rep q
  have hYζ : squareZeroAlgebraExtensionClassesEquivExtOne S.A' S.B S.N
      (Quotient.mk (SquareZeroExtensionProblem.CompatibleExtension.isomorphicSetoid
        (algebraExtensionProblem S.A' S.B S.N)) Y) = ζ := by
    rwa [hY]
  have hmap : ∀ i : S.I, kernelInclusion Y (S.c i) = algebraMap S.A' Y.B' i :=
    (towerMap_eq_iff_mapOnIdeal S Y).1 (by rwa [hYζ])
  refine ⟨Quotient.mk (SquareZeroExtensionProblem.CompatibleExtension.isomorphicSetoid S)
    (ofMapOnIdeal S Y hmap), Subtype.ext ?_⟩
  rw [solutionClassMap_mk, solutionExtClass, forgetMapOnIdeal_ofMapOnIdeal]
  exact hYζ

/-- **Stacks 0GPX.**  Let `0 → I → A' → A → 0`, `A → B` and `c : I → N` be as in
**Stacks 08S4**, and let `ξ ∈ Ext¹_A(NL_{A/A'}, I)` be the class of the extension `A'` of `A`
by `I` under **Stacks 0GPT**.  The set of isomorphism classes of solutions of the extension
problem is canonically bijective to the fibre of
`Ext¹_B(NL_{B/A'}, N) → Ext¹_A(NL_{A/A'}, N)` over the image of `ξ`.

The bijection is the canonical one: it sends the class of a solution to the class of its
underlying square-zero extension of the `A'`-algebra `B` by `N`, as recorded by
`solutionsEquivFibre_apply`. -/
@[stacks 0GPX "solutions with middle ring in the universe max uB uN, as in Lemma 0GPT"]
public def solutionsEquivFibre :
    SquareZeroExtensionProblem.CompatibleExtension.IsomorphismClasses.{u₁, u₂, u₃, u₄,
      max u₃ u₄} S ≃ solutionsFibre S :=
  Equiv.ofBijective (solutionClassMap S)
    ⟨solutionClassMap_injective S, solutionClassMap_surjective S⟩

/-- The bijection of **Stacks 0GPX** sends the class of a solution to the class in
`Ext¹_B(NL_{B/A'}, N)` of its underlying square-zero extension of the `A'`-algebra `B` by
`N`. -/
@[stacks 0GPX "the bijection sends a solution to the class of its underlying extension"]
public lemma solutionsEquivFibre_apply (P : S.CompatibleExtension.{max u₃ u₄}) :
    (solutionsEquivFibre S (Quotient.mk
      (SquareZeroExtensionProblem.CompatibleExtension.isomorphicSetoid S) P)).1
      = solutionExtClass S P := rfl

end Stacks.Deformation

end
