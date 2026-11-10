module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FormalSpace.Affine.Types
public import StacksFrontier.AlgebraicGeometry.FormalSpace.CountablePresentation
public import StacksFrontier.AlgebraicGeometry.FormalSpace.CountablyIndexed
public import StacksFrontier.AlgebraicGeometry.FormalSpace.McQuillan
public import StacksFrontier.AlgebraicGeometry.FormalSpace.SectionLimitPresentation
public import StacksFrontier.AlgebraicGeometry.FormalSpace.SpectrumPresentation
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.ThickeningAffine
public import StacksFrontier.Topology.Algebra.AdicTopology.SequentialLimit

/-!
# A countably indexed affine formal algebraic space is McQuillan (Stacks 0AIK)

An affine formal algebraic space which admits a presentation indexed by `ℕ` has a
presentation whose ring of global sections surjects onto the sections of every stage.

## Main results

* `AlgebraicGeometry.FormalSpace.hasSomeSurjectivePresentation_of_isCountablyIndexed`:
  a presentation whose section projections are surjective, which is condition (4) of
  Stacks 0AIC.
* `AlgebraicGeometry.FormalSpace.exists_quotientSystem_of_isCountablyIndexed`: the presenting
  ring, as the limit of the section rings of a sequential presentation.
* `AlgebraicGeometry.FormalSpace.isPresentingRing_of_isCountablyIndexed`:
  **Stacks 0AIK**, item (6).

## Implementation notes

Being McQuillan is Stacks 0AID. Both halves are produced here: condition (4) of Stacks 0AIC,
`AlgebraicGeometry.FormalSpace.HasSomeSurjectivePresentation`, which is what the source's proof
of item (6) produces directly, and condition (1), that the space is the formal spectrum of a
weakly admissible ring. The second comes from the limit of the section rings of a sequential
presentation, topologized by the kernels of its projections, together with the recognition
statement of `StacksFrontier.AlgebraicGeometry.FormalSpace.SectionLimitPresentation`.

The proof is the source's. A countably indexed sheaf has a presentation indexed by a countable
nonempty directed preorder (**Stacks 0AII**,
`AlgebraicGeometry.FormalSpace.isCountablyIndexed_iff_exists_countable_presentation`; the
detour through a general countable index rather than `ℕ` is forced, because the index of a
presentation must live in `Type (u + 1)`). Its transition morphisms are thickenings, hence
closed immersions of affine schemes, hence surjective on global sections. So the section rings
form a countable directed inverse system of surjections, and the projections from its limit are
surjective.

That last step strengthens `section_of_surjective_invsystem`
(`StacksFrontier/Algebra/MittagLeffler/InverseSystem.lean`), which produces *some* compatible
family, to one taking a prescribed value at a prescribed index. It is obtained by applying
that lemma to the subsystem of elements which agree with the prescribed value after a common
refinement, and is stated for an arbitrary set-valued system.

## References

* [Stacks Project, Tag 0AIK](https://stacks.math.columbia.edu/tag/0AIK)
* [Stacks Project, Tag 0AIC](https://stacks.math.columbia.edu/tag/0AIC)
* [Stacks Project, Tag 0AII](https://stacks.math.columbia.edu/tag/0AII)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.FormalSpace

universe u v w

/-- A countable directed inverse system of sets with surjective transition maps has a
compatible family taking any prescribed value at any prescribed index: the projections from
its limit are surjective. -/
private theorem exists_compatible_family_eq
    {I : Type v} [Preorder I] [Countable I] [Nonempty I] [IsDirected I (· ≤ ·)]
    (A : I → Type w) (t : ⦃i j : I⦄ → i ≤ j → A j → A i)
    (hid : ∀ (i : I) (x : A i), t (le_refl i) x = x)
    (hcomp : ∀ ⦃i j k : I⦄ (hij : i ≤ j) (hjk : j ≤ k) (x : A k),
      t hij (t hjk x) = t (le_trans hij hjk) x)
    (hsurj : ∀ ⦃i j : I⦄ (h : i ≤ j), Function.Surjective (t h))
    (i₀ : I) (a : A i₀) :
    ∃ s : ∀ i, A i, (∀ ⦃i j : I⦄ (h : i ≤ j), t h (s j) = s i) ∧ s i₀ = a := by
  let E : I → Type w := fun i =>
    {x : A i // ∃ (k : I) (hik : i ≤ k) (h₀k : i₀ ≤ k) (y : A k),
      t hik y = x ∧ t h₀k y = a}
  let v : ⦃i j : I⦄ → i ≤ j → E j → E i := fun {i j} hij x =>
    ⟨t hij x.1, by
      obtain ⟨k, hjk, h₀k, y, hyx, hya⟩ := x.2
      exact ⟨k, hij.trans hjk, h₀k, y, (hcomp hij hjk y).symm.trans (congrArg (t hij) hyx), hya⟩⟩
  have v_surj {i j : I} (hij : i ≤ j) : Function.Surjective (v hij) := by
    intro x
    obtain ⟨k, hik, h₀k, y, hyx, hya⟩ := x.2
    obtain ⟨l, hjl, hkl⟩ := directed_of (· ≤ ·) j k
    obtain ⟨z, hz⟩ := hsurj hkl y
    refine ⟨⟨t hjl z, ?_⟩, ?_⟩
    · exact ⟨l, hjl, h₀k.trans hkl, z, rfl, (hcomp h₀k hkl z).symm.trans (by rw [hz, hya])⟩
    · apply Subtype.ext
      calc
        t hij (t hjl z) = t (hij.trans hjl) z := hcomp hij hjl z
        _ = t (hik.trans hkl) z := rfl
        _ = t hik (t hkl z) := (hcomp hik hkl z).symm
        _ = t hik y := by rw [hz]
        _ = x.1 := hyx
  have v_nonempty (i : I) : Nonempty (E i) := by
    obtain ⟨k, hik, h₀k⟩ := directed_of (· ≤ ·) i i₀
    obtain ⟨y, hy⟩ := hsurj h₀k a
    exact ⟨⟨t hik y, ⟨k, hik, h₀k, y, rfl, hy⟩⟩⟩
  obtain ⟨s, hs⟩ := section_of_surjective_invsystem (I := I) (S := E)
    (t := v) (hid := fun i x ↦ Subtype.ext (hid i x.1))
    (hcomp := fun _ _ _ hij hjk x ↦ Subtype.ext (hcomp hij hjk x.1))
    (hsurj := fun _ _ h ↦ v_surj h) (hne := v_nonempty)
  refine ⟨fun i => (s i).1, fun i j h => congrArg Subtype.val (hs h), ?_⟩
  obtain ⟨k, hik, h₀k, y, hyx, hya⟩ := (s i₀).2
  exact hyx.symm.trans hya

/-- A thickening of an affine scheme is surjective on global sections. -/
private theorem surjective_appTop_of_isThickening {Y Z : Scheme.{u}} [IsAffine Z] {i : Y ⟶ Z}
    (hi : Stacks.Thickenings.IsThickening i) : Function.Surjective i.appTop :=
  have := hi.1
  (IsClosedImmersion.isAffine_surjective_of_isAffine i).2

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Stacks Project, Tag 0AIK**, item (6). A countably indexed affine formal algebraic space
is McQuillan: it has a presentation by affine thickenings all of whose section-ring projections
are surjective, which is condition (4) of Stacks 0AIC. -/
@[stacks 0AIK "countable_mcquillan"]
theorem hasSomeSurjectivePresentation_of_isCountablyIndexed {X : FppfSheaf B S hS}
    (hX : IsAffineFormalAlgebraicSpace B S hS X) (hc : IsCountablyIndexed B S hS X) :
    HasSomeSurjectivePresentation B S hS X := by
  obtain ⟨I, pre, hne, hdir, hcnt, D, hthick, hcolim⟩ :=
    (isCountablyIndexed_iff_exists_countable_presentation B S hS X).mp hc
  refine ⟨hX, I, pre, hne, hdir, D, hthick, hcolim, ?_⟩
  let F : Iᵒᵖ ⥤ Type u := sectionDiagram B S hS D ⋙ forget CommRingCat
  let t : ⦃i j : I⦄ → i ≤ j → F.obj (Opposite.op j) → F.obj (Opposite.op i) :=
    fun {_ _} h => F.map (homOfLE h).op
  have tid (i : I) (x : F.obj (Opposite.op i)) : t (le_refl i) x = x := by simp [t]
  have tcomp ⦃i j k : I⦄ (hij : i ≤ j) (hjk : j ≤ k) (x : F.obj (Opposite.op k)) :
      t hij (t hjk x) = t (le_trans hij hjk) x := by
    have heq : (homOfLE hjk).op ≫ (homOfLE hij).op =
        (homOfLE (le_trans hij hjk)).op := Subsingleton.elim _ _
    change (F.map (homOfLE hjk).op ≫ F.map (homOfLE hij).op) x =
      F.map (homOfLE (le_trans hij hjk)).op x
    rw [← F.map_comp, heq]
  have tsurj ⦃i j : I⦄ (hij : i ≤ j) : Function.Surjective (t hij) := by
    exact surjective_appTop_of_isThickening
      (i := (BigAffineFppf.toScheme B S hS).map (D.map (homOfLE hij))) (hthick (homOfLE hij))
  intro i a
  obtain ⟨s, hs, hsi⟩ := exists_compatible_family_eq
    (fun i => F.obj (Opposite.op i)) t tid tcomp tsurj i a
  refine ⟨⟨fun j => s j.unop, fun {_ _} f => ?_⟩, hsi⟩
  rw [Subsingleton.elim f (homOfLE (leOfHom f.unop)).op]
  exact hs _

/-! ### The presenting ring of a sequential presentation -/

/-- The ideal of a thickening of a quasi-compact scheme by an affine one consists of nilpotent
global sections. -/
theorem locallyNilpotent_ker_appTop_of_isThickening {Y Z : Scheme.{u}} [CompactSpace Z]
    {i : Y ⟶ Z} (hi : Stacks.Thickenings.IsThickening i) :
    (RingHom.ker i.appTop.hom).LocallyNilpotent :=
  fun _ ha ↦ hi.isNilpotent_of_mem_ker_appTop_of_compactSpace ha

/-- A countably indexed affine formal algebraic space is the formal spectrum of the limit of
the section rings of a sequential presentation, a weakly admissible topological ring with a
countable fundamental system of neighbourhoods of `0`.

The transition morphisms of the presentation are thickenings of affine schemes, so they are
surjective on sections with nil kernel; hence the projections of the limit are surjective,
their kernels are weak ideals of definition basing the topology, and the recognition statement
for a sequential presentation identifies the space with the formal spectrum. -/
theorem exists_quotientSystem_of_isCountablyIndexed {X : FppfSheaf B S hS}
    (hc : IsCountablyIndexed B S hS X) :
    ∃ (A : Type u) (_ : CommRing A) (_ : TopologicalSpace A) (_ : IsTopologicalRing A)
      (_ : IsLinearTopology A A) (Q : QuotientSystem B S hS A),
      TopologicalRing.IsWeaklyAdmissible A ∧ (nhds (0 : A)).IsCountablyGenerated ∧
        Nonempty (X ≅ formalSpectrum Q) := by
  obtain ⟨D, hD, ⟨e⟩⟩ := hc
  let Rn : ℕ → Type u := fun n ↦ Γ((BigAffineFppf.toScheme B S hS).obj (D.obj n), ⊤)
  let t : ∀ n : ℕ, Rn (n + 1) →+* Rn n := fun n ↦
    (((BigAffineFppf.toScheme B S hS).map (D.map (homOfLE (Nat.le_succ n)))).appTop).hom
  have hthick (n : ℕ) : Stacks.Thickenings.IsThickening
      ((BigAffineFppf.toScheme B S hS).map (D.map (homOfLE (Nat.le_succ n)))) :=
    hD (homOfLE (Nat.le_succ n))
  have hsurj (n : ℕ) : Function.Surjective (t n) :=
    surjective_appTop_of_isThickening (hthick n)
  have hnil (n : ℕ) : (RingHom.ker (t n)).LocallyNilpotent :=
    locallyNilpotent_ker_appTop_of_isThickening (hthick n)
  refine ⟨TopologicalRing.SequentialLimit t, inferInstance, inferInstance, inferInstance,
    inferInstance, ?_⟩
  let P : SequentialQuotients B S hS X (TopologicalRing.SequentialLimit t) :=
    { diagram := D
      isThickening := hD
      colimitIso := e
      proj := TopologicalRing.SequentialLimit.proj t
      proj_surjective := TopologicalRing.SequentialLimit.proj_surjective t hsurj
      proj_comp := TopologicalRing.SequentialLimit.proj_comp t
      isWeakIdealOfDefinition_ker :=
        TopologicalRing.SequentialLimit.isWeakIdealOfDefinition_ker t hnil
      hasBasis_nhds_zero := TopologicalRing.SequentialLimit.hasBasis_nhds_zero t }
  obtain ⟨Q, hQ⟩ := P.exists_quotientSystem_formalSpectrum_iso
  exact ⟨Q, TopologicalRing.SequentialLimit.isWeaklyAdmissible t hnil,
    (TopologicalRing.SequentialLimit.hasBasis_nhds_zero t).isCountablyGenerated, hQ⟩

/-- **Stacks Project, Tag 0AIK**, item (6). A countably indexed affine formal algebraic space
is McQuillan: it has a presentation by affine thickenings all of whose section-ring projections
are surjective, which is condition (4) of Stacks 0AIC, and it is the formal spectrum of a
weakly admissible topological ring, which is condition (1). -/
@[stacks 0AIK "(6), countably indexed implies McQuillan"]
theorem isPresentingRing_of_isCountablyIndexed {X : FppfSheaf B S hS}
    (hX : IsAffineFormalAlgebraicSpace B S hS X) (hc : IsCountablyIndexed B S hS X) :
    HasSomeSurjectivePresentation B S hS X ∧
      ∃ (A : Type u) (_ : CommRing A) (_ : TopologicalSpace A) (_ : IsTopologicalRing A)
        (_ : IsLinearTopology A A), IsPresentingRing B S hS A X := by
  refine ⟨hasSomeSurjectivePresentation_of_isCountablyIndexed B S hS hX hc, ?_⟩
  obtain ⟨A, hCR, hTS, hTR, hLT, Q, hWA, -, ⟨e⟩⟩ :=
    exists_quotientSystem_of_isCountablyIndexed B S hS hc
  refine ⟨A, hCR, hTS, hTR, hLT, hWA, ⟨?_⟩⟩
  exact { Q.weakIdealColimitPresentation with
    colimitIso := e ≪≫ Q.weakIdealColimitPresentation.colimitIso }

end AlgebraicGeometry.FormalSpace

end
