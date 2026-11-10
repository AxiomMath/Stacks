module

public import StacksFrontier.AlgebraicGeometry.Divisors.AssociatedPoints.Quasicoherent
public import StacksFrontier.AlgebraicGeometry.Divisors.AssociatedPoints.Vanishing
public import StacksFrontier.Topology.Sheaves.Cohomology.KFlat.FlatModuleSheavesAndStalks
public import StacksFrontier.RingTheory.Ideal.AssociatedPrime.WeaklyAssociated
public import StacksCore.Tactic.StacksAttribute

/-!
# Detecting a monomorphism at the weakly associated points

A map of quasi-coherent modules on a scheme is a monomorphism as soon as its map on stalks is
injective at every weakly associated point of its source.

## Main results

* `AlgebraicGeometry.stalk_map_injective_of_mono`: a monomorphism of sheaves of modules is
  injective on stalks.
* `AlgebraicGeometry.weaklyAssociatedPoints_subset_of_mono`: a monomorphism of sheaves of
  modules induces an inclusion of weakly associated points.
* `AlgebraicGeometry.mono_of_stalk_injective_on_weaklyAssociatedPoints` is the criterion.

## Implementation notes

Injectivity of the sheaf morphism is the categorical predicate `CategoryTheory.Mono`, and the
stalk map is the map of additive commutative groups induced by the underlying map of presheaves
of modules. The criterion is proved by showing that the kernel, which is again quasi-coherent,
has no weakly associated point, hence is zero by Stacks tag 05AP.

## References

* [Stacks Project, Tag 0AVP](https://stacks.math.columbia.edu/tag/0AVP)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry

/-- A monomorphism of sheaves of modules on a scheme is injective on every stalk. -/
lemma stalk_map_injective_of_mono {X : Scheme.{u}} {F G : X.Modules} (f : F ⟶ G) [Mono f]
    (x : X) :
    Function.Injective (((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
      ((PresheafOfModules.toPresheaf X.ringCatSheaf.obj).map f.val)).hom) := by
  let g := (PresheafOfModules.toPresheaf X.ringCatSheaf.obj).map f.val
  have hg : Mono g := @OXModule.mono_val_of_mono _ F G f ‹Mono f›
  have hcomp : ∀ V : X.Opens, Function.Injective (g.app (op V)) := fun V =>
    AddCommGrpCat.mono_iff_injective _ |>.mp ((NatTrans.mono_iff_mono_app g).mp hg (op V))
  exact TopCat.Presheaf.stalkFunctor_map_injective_of_app_injective hcomp x

/-- A monomorphism of sheaves of modules carries weakly associated points to weakly associated
points. -/
lemma weaklyAssociatedPoints_subset_of_mono {X : Scheme.{u}} {F G : X.Modules} (i : F ⟶ G)
    [Mono i] :
    Stacks.Divisors.weaklyAssociatedPoints F ⊆ Stacks.Divisors.weaklyAssociatedPoints G := by
  intro x hx
  rw [Stacks.Divisors.mem_weaklyAssociatedPoints_iff] at hx ⊢
  change IsWeaklyAssociatedPrime _ (OXModule.stalk F x) _ at hx
  change IsWeaklyAssociatedPrime _ (OXModule.stalk G x) _
  exact Module.weaklyAssociatedPrimes_subset_of_injective
    (f := OXModule.stalkLinearMap F G i x) (stalk_map_injective_of_mono i x) hx

/-- **Stacks Project, Tag 0AVP.** A map of quasi-coherent modules is a monomorphism if its map
on stalks is injective at every weakly associated point of its source. -/
@[stacks 0AVP]
theorem mono_of_stalk_injective_on_weaklyAssociatedPoints {X : Scheme.{u}} {F G : X.Modules}
    [F.IsQuasicoherent] [G.IsQuasicoherent] (f : F ⟶ G)
    (hf : ∀ x : X,
      (Function.Injective
        ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
          ((PresheafOfModules.toPresheaf X.ringCatSheaf.obj).map f.val)).hom) ∨
        x ∉ Stacks.Divisors.weaklyAssociatedPoints F) :
    Mono f := by
  let K := kernel f
  let i : K ⟶ F := kernel.ι f
  have hempty : Stacks.Divisors.weaklyAssociatedPoints K = ∅ := by
    ext x
    simp only [Set.mem_empty_iff_false, iff_false]
    intro hx
    rcases hf x with hinj | hnot
    · rw [Stacks.Divisors.mem_weaklyAssociatedPoints_iff] at hx
      change IsWeaklyAssociatedPrime (X.presheaf.stalk x) (OXModule.stalk K x)
        (IsLocalRing.maximalIdeal (X.presheaf.stalk x)) at hx
      let T := TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x
      let q := PresheafOfModules.toPresheaf X.ringCatSheaf.obj
      have hzero : ∀ a : T.obj K.val.presheaf, (T.map (q.map f.val)).hom
          ((T.map (q.map i.val)).hom a) = 0 := by
        intro a
        have hcomp0 : i.val ≫ f.val = 0 := congrArg (fun g => g.val) (kernel.condition f)
        have h : (T.map (q.map (i.val ≫ f.val))).hom a = 0 := by
          rw [hcomp0, q.map_zero, T.map_zero]
          rfl
        rwa [q.map_comp, T.map_comp, AddCommGrpCat.hom_comp] at h
      have hzeroi : ∀ a : T.obj K.val.presheaf, (T.map (q.map i.val)).hom a = 0 :=
        fun a => hinj (by rw [hzero a, map_zero])
      have hsubsingleton : Subsingleton (OXModule.stalk K x) :=
        ⟨fun a b => stalk_map_injective_of_mono i x (by rw [hzeroi a, hzeroi b])⟩
      obtain ⟨m, hm⟩ := hx
      obtain rfl : m = 0 := hsubsingleton.elim _ _
      simp [Submodule.annihilator_bot, Ideal.minimalPrimes_top] at hm
    · exact hnot (weaklyAssociatedPoints_subset_of_mono i hx)
  exact CategoryTheory.Preadditive.mono_of_isZero_kernel f
    ((isZero_iff_weaklyAssociatedPoints_eq_empty K).2 hempty)

end AlgebraicGeometry
