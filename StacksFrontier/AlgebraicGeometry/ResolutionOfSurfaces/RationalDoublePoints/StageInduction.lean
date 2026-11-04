module

public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.RationalDoublePoints.PointBlowupLocalization
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.RationalDoublePoints.ResolutionStages
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.RationalDoublePoints.SingularPointBlowupChain
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.Resolution.SingularPointBlowupChainResolution
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.QuadraticTransformations.PointBlowupChain
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.ModifyingLocalRings.NormalizedPointBlowupSequence
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.Completion.StalkBaseChangePullback

/-!
# From the blowup of one rational double point to a sequence of blowups of a surface

The source resolves a rational double point `A` by a finite sequence of blowups in singular closed
points `Xₙ → ⋯ → X₁ → X₀ = Spec(A)` each stage of which is normal with finitely many singular
points of the same type. All the work is local: what happens when one blows up the maximal ideal
of a single rational double point. This file assembles the sequence out of that local
information.

The local information is the following, for every rational double point `S` (a Situation
[Stacks, Tag 0BGC]) with blowup `X_S` of `Spec(S.A)` in the maximal ideal:

* `X_S` is normal, has finitely many singular points, each closed, lying over the closed point,
  and with local ring again a rational double point;
* the relation `T ≺ S` — "`T.A` is the local ring at a singular point of `X_S`", taken up to
  isomorphism of completions — is well founded.

Given these, a scheme each of whose stages has finitely many singular points with rational double
point local rings is resolved by blowing up its singular points one at a time: blowing up a
closed point `y` changes nothing away from `y` and replaces, over `y`, the local ring at `y` by
the local rings at the singular points of `X_{𝒪_{Y, y}}`, which are `≺`-smaller. The multiset of
isomorphism classes of the singular local rings therefore decreases for the multiset extension of
`≺` (`Relation.CutExpand`), which is well founded.

## Main definitions

* `AlgebraicGeometry.HasRationalDoublePointSingularities`: a normal scheme with finitely many
  singular points, each of whose local rings is the ring of a Situation 0BGC — the property the
  source asks of every stage (the library's `AlgebraicGeometry.IsRationalDoublePointStage` also
  asks for local Noetherianity and dimension at most two).
* `AlgebraicGeometry.IsRationalDoublePointStageNoetherian`: that property, together with
  Noetherianity and closedness of the singular points, which is what the induction carries.
* `AlgebraicGeometry.RationalDoublePointSituation.BlowUpRel`: the relation `≺`.

## Main results

* `AlgebraicGeometry.exists_singularPointBlowupChain_isRegular_of_blowUpRel`: the assembly.
-/

@[expose] public noncomputable section

open CategoryTheory IsLocalRing TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- The property the source asks of every stage of the resolution of a rational double point:
the stage is normal and has finitely many singular points, the local ring at each of which is
the ring of a Situation [Stacks, Tag 0BGC] ("singular points of the same type"). -/
def HasRationalDoublePointSingularities (Y : Scheme.{u}) : Prop :=
  IsNormal Y ∧ (singularLocus Y).Finite ∧
    ∀ y ∈ singularLocus Y, ∃ S : RationalDoublePointSituation.{u},
      Nonempty (S.A ≃+* Y.presheaf.stalk y)

/-- `AlgebraicGeometry.HasRationalDoublePointSingularities` together with Noetherianity and
closedness of the singular points. -/
def IsRationalDoublePointStageNoetherian (Y : Scheme.{u}) : Prop :=
  IsNoetherian Y ∧ HasRationalDoublePointSingularities Y ∧
    ∀ y ∈ singularLocus Y, IsClosed ({y} : Set Y)

namespace RationalDoublePointSituation

/-- The completion of a local ring along its maximal ideal. -/
abbrev localCompletion (R : Type u) [CommRing R] [IsLocalRing R] : Type u :=
  AdicCompletion (IsLocalRing.maximalIdeal R) R

/-- `T ≺ S`: the completion of the ring of `T` is the completion of the local ring at a singular
point of the blowup in its maximal ideal of the spectrum of a ring whose completion is that of the
ring of `S`.

Only completions enter, so that `≺` is a relation between the complete rational double points:
the local rings at the closed points of the blowup of `Spec(A)` have the completions of those of
the blowup of `Spec(A^)` ([Stacks, Tag 0BG5]). -/
def BlowUpRel (T S : RationalDoublePointSituation.{u}) : Prop :=
  ∃ S' : RationalDoublePointSituation.{u}, Nonempty (localCompletion S'.A ≃+* localCompletion S.A) ∧
    ∃ x : blowUp (maximalIdealSheaf S'.A), x ∈ singularLocus (blowUp (maximalIdealSheaf S'.A)) ∧
      Nonempty (localCompletion T.A ≃+*
        localCompletion ((blowUp (maximalIdealSheaf S'.A)).presheaf.stalk x))

/-- Isomorphism of the completions of the rings of two situations. -/
def isoSetoid : Setoid RationalDoublePointSituation.{u} where
  r S T := Nonempty (localCompletion S.A ≃+* localCompletion T.A)
  iseqv := ⟨fun _ => ⟨RingEquiv.refl _⟩, fun ⟨e⟩ => ⟨e.symm⟩, fun ⟨e⟩ ⟨f⟩ => ⟨e.trans f⟩⟩

/-- The relation `≺` on isomorphism classes. -/
def BlowUpRelClass : Quotient isoSetoid.{u} → Quotient isoSetoid.{u} → Prop :=
  Quotient.lift₂ BlowUpRel (by
    rintro T S T' S' ⟨eT⟩ ⟨eS⟩
    exact propext
      ⟨fun ⟨S'', ⟨e⟩, x, hx, ⟨f⟩⟩ => ⟨S'', ⟨e.trans eS⟩, x, hx, ⟨eT.symm.trans f⟩⟩,
        fun ⟨S'', ⟨e⟩, x, hx, ⟨f⟩⟩ => ⟨S'', ⟨e.trans eS.symm⟩, x, hx, ⟨eT.trans f⟩⟩⟩)

/-- If `≺` is well founded, so is the induced relation on isomorphism classes. -/
theorem wellFounded_blowUpRelClass (h : WellFounded BlowUpRel.{u}) :
    WellFounded BlowUpRelClass.{u} := by
  refine ⟨fun a => ?_⟩
  induction a using Quotient.ind with
  | _ S =>
    induction S using h.induction with
    | _ S ih =>
      refine ⟨_, fun b hb => ?_⟩
      induction b using Quotient.ind with
      | _ T => exact ih T hb

end RationalDoublePointSituation

/-- The blowup of every rational double point in its maximal ideal is normal, with finitely many
singular points, each closed, over the closed point, and a rational double point again. -/
def RationalDoublePointBlowUpProperties : Prop :=
  ∀ S : RationalDoublePointSituation.{u},
    IsNormal (blowUp (maximalIdealSheaf S.A)) ∧
      (singularLocus (blowUp (maximalIdealSheaf S.A))).Finite ∧
      ∀ x ∈ singularLocus (blowUp (maximalIdealSheaf S.A)),
        IsClosed ({x} : Set (blowUp (maximalIdealSheaf S.A))) ∧
          blowUpToBase (maximalIdealSheaf S.A) x = closedPoint S.A ∧
          ∃ T : RationalDoublePointSituation.{u},
            Nonempty (T.A ≃+* (blowUp (maximalIdealSheaf S.A)).presheaf.stalk x)

namespace RationalDoublePointSituation

/-- The relation `≺` on isomorphism classes, extended to `Option` by an isolated bottom element
`none`, which stands for the class of a point without rational double point local ring. -/
def BlowUpRelOption : Option (Quotient isoSetoid.{u}) → Option (Quotient isoSetoid.{u}) → Prop
  | some a, some b => BlowUpRelClass a b
  | _, _ => False

/-- If `≺` is well founded, so is its extension to `Option` of the isomorphism classes. -/
theorem wellFounded_blowUpRelOption (h : WellFounded BlowUpRel.{u}) :
    WellFounded BlowUpRelOption.{u} := by
  refine ⟨fun a => ?_⟩
  cases a with
  | none => exact ⟨_, fun b hb => by cases b <;> exact hb.elim⟩
  | some a =>
    induction a using (wellFounded_blowUpRelClass h).induction with
    | _ a ih =>
      refine ⟨_, fun b hb => ?_⟩
      cases b with
      | none => exact hb.elim
      | some b => exact ih b hb

end RationalDoublePointSituation

open RationalDoublePointSituation

open scoped Classical in
/-- The isomorphism class of the local ring at a point, when it is the ring of a Situation
0BGC. -/
def stalkClass (Y : Scheme.{u}) (y : Y) : Option (Quotient isoSetoid.{u}) :=
  if h : ∃ S : RationalDoublePointSituation.{u}, Nonempty (S.A ≃+* Y.presheaf.stalk y) then
    some (Quotient.mk _ h.choose)
  else none

open scoped Classical in
/-- If the local ring at `y` is isomorphic to the ring of `S`, then the class of the local ring at
`y` is the class of `S`. -/
theorem stalkClass_eq_some {Y : Scheme.{u}} {y : Y} (S : RationalDoublePointSituation.{u})
    (e : S.A ≃+* Y.presheaf.stalk y) : stalkClass Y y = some (Quotient.mk _ S) := by
  have h : ∃ S : RationalDoublePointSituation.{u}, Nonempty (S.A ≃+* Y.presheaf.stalk y) :=
    ⟨S, ⟨e⟩⟩
  rw [stalkClass, dite_eq_left h]
  exact congrArg some (Quotient.sound
    ⟨(StacksDraft.exists_adicCompletion_ringEquiv_of_ringEquiv
      (h.choose_spec.some.trans e.symm)).choose⟩)

open scoped Classical in
/-- Points with isomorphic local rings have the same class. -/
theorem stalkClass_congr {Y Z : Scheme.{u}} {y : Y} {z : Z}
    (e : Y.presheaf.stalk y ≃+* Z.presheaf.stalk z) : stalkClass Y y = stalkClass Z z := by
  by_cases h : ∃ S : RationalDoublePointSituation.{u}, Nonempty (S.A ≃+* Y.presheaf.stalk y)
  · obtain ⟨S, ⟨f⟩⟩ := h
    rw [stalkClass_eq_some S f, stalkClass_eq_some S (f.trans e)]
  · have h' : ¬ ∃ S : RationalDoublePointSituation.{u}, Nonempty (S.A ≃+* Z.presheaf.stalk z) :=
      fun ⟨S, ⟨f⟩⟩ => h ⟨S, ⟨f.trans e.symm⟩⟩
    rw [stalkClass, dite_eq_right h, stalkClass, dite_eq_right h']

open scoped Classical in
/-- The multiset of isomorphism classes of the local rings at the singular points of a stage. -/
def stageMultiset (Y : Scheme.{u}) : Multiset (Option (Quotient isoSetoid.{u})) :=
  if h : (singularLocus Y).Finite then h.toFinset.val.map (stalkClass Y) else 0

/-- A ring isomorphism carries regularity. -/
theorem isRegularLocalRing_iff_of_ringEquiv {R R' : Type*} [CommRing R] [CommRing R']
    [IsLocalRing R] [IsLocalRing R'] (e : R ≃+* R') :
    IsRegularLocalRing R ↔ IsRegularLocalRing R' :=
  ⟨fun _ => IsRegularLocalRing.of_ringEquiv e, fun _ => IsRegularLocalRing.of_ringEquiv e.symm⟩

/-- A morphism of schemes that is an isomorphism on stalks at `x` identifies the local rings. -/
private theorem nonempty_ringEquiv_stalk_of_isIso_stalkMap {X Y : Scheme.{u}} (f : X ⟶ Y) (x : X)
    [IsIso (f.stalkMap x)] : Nonempty (Y.presheaf.stalk (f x) ≃+* X.presheaf.stalk x) :=
  ⟨(asIso (f.stalkMap x)).commRingCatIsoToRingEquiv⟩

/-- A morphism of schemes that is an isomorphism on stalks at `x` preserves singularity at `x`. -/
private theorem mem_singularLocus_iff_of_isIso_stalkMap {X Y : Scheme.{u}} (f : X ⟶ Y) (x : X)
    [IsIso (f.stalkMap x)] : f x ∈ singularLocus Y ↔ x ∈ singularLocus X :=
  not_congr (isRegularLocalRing_iff_of_ringEquiv
    (nonempty_ringEquiv_stalk_of_isIso_stalkMap f x).some)

section BlowUpOffCentre

variable {W : Scheme.{u}} (w : W) (hwc : IsClosed ({w} : Set W))

/-- Off the blown-up closed point, the local rings of the blowup are those of the base. -/
theorem nonempty_ringEquiv_stalk_blowUpToBase_of_ne
    (z : blowUp (Scheme.IdealSheafData.vanishingIdeal (⟨{w}, hwc⟩ : Closeds W)))
    (hz : blowUpToBase (Scheme.IdealSheafData.vanishingIdeal (⟨{w}, hwc⟩ : Closeds W)) z ≠ w) :
    Nonempty ((blowUp
      (Scheme.IdealSheafData.vanishingIdeal (⟨{w}, hwc⟩ : Closeds W))).presheaf.stalk z ≃+*
        W.presheaf.stalk
        (blowUpToBase (Scheme.IdealSheafData.vanishingIdeal (⟨{w}, hwc⟩ : Closeds W)) z)) := by
  have := isIso_stalkMap_blowUpToBase_of_ne w hwc z hz
  exact ⟨(nonempty_ringEquiv_stalk_of_isIso_stalkMap _ z).some.symm⟩

/-- Off the blown-up closed point, a point of the blowup is singular iff its image is. -/
theorem mem_singularLocus_blowUp_iff_of_ne
    (z : blowUp (Scheme.IdealSheafData.vanishingIdeal (⟨{w}, hwc⟩ : Closeds W)))
    (hz : blowUpToBase (Scheme.IdealSheafData.vanishingIdeal (⟨{w}, hwc⟩ : Closeds W)) z ≠ w) :
    z ∈ singularLocus (blowUp (Scheme.IdealSheafData.vanishingIdeal (⟨{w}, hwc⟩ : Closeds W))) ↔
      blowUpToBase (Scheme.IdealSheafData.vanishingIdeal (⟨{w}, hwc⟩ : Closeds W)) z ∈
        singularLocus W :=
  have := isIso_stalkMap_blowUpToBase_of_ne w hwc z hz
  (mem_singularLocus_iff_of_isIso_stalkMap _ z).symm

/-- Off the blown-up closed point, a point of the blowup is closed if its image is. -/
theorem isClosed_singleton_blowUp_of_ne
    {z : blowUp (Scheme.IdealSheafData.vanishingIdeal (⟨{w}, hwc⟩ : Closeds W))}
    (hz : blowUpToBase (Scheme.IdealSheafData.vanishingIdeal (⟨{w}, hwc⟩ : Closeds W)) z ≠ w)
    (h : IsClosed ({blowUpToBase (Scheme.IdealSheafData.vanishingIdeal (⟨{w}, hwc⟩ : Closeds W)) z}
      : Set W)) :
    IsClosed ({z} : Set
      (blowUp (Scheme.IdealSheafData.vanishingIdeal (⟨{w}, hwc⟩ : Closeds W)))) := by
  set b := blowUpToBase (Scheme.IdealSheafData.vanishingIdeal (⟨{w}, hwc⟩ : Closeds W))
  have hset : ({z} : Set _) = b.base ⁻¹' {b z} := by
    ext z'
    simp only [Set.mem_singleton_iff, Set.mem_preimage]
    exact ⟨fun h => h ▸ rfl, fun h => (blowUpToBase_injective_of_ne w hwc hz h.symm).symm⟩
  rw [hset]
  exact h.preimage b.continuous

open scoped Classical in
/-- Off the blown-up point, the classes of the singular local rings of the blowup are those of
the singular local rings of `W` other than `w`. -/
theorem map_stalkClass_filter_ne_blowUp (hfin : (singularLocus W).Finite)
    (hfin' : (singularLocus
      (blowUp (Scheme.IdealSheafData.vanishingIdeal (⟨{w}, hwc⟩ : Closeds W)))).Finite) :
    (hfin'.toFinset.val.filter (fun z => ¬ blowUpToBase
        (Scheme.IdealSheafData.vanishingIdeal (⟨{w}, hwc⟩ : Closeds W)) z = w)).map
      (stalkClass _) = (hfin.toFinset.erase w).val.map (stalkClass W) := by
  set I := Scheme.IdealSheafData.vanishingIdeal (⟨{w}, hwc⟩ : Closeds W)
  set b := blowUpToBase I
  set F := hfin.toFinset with hF
  set F' := hfin'.toFinset with hF'
  have h1 : (F'.val.filter (fun z => ¬ b z = w)).map (stalkClass (blowUp I)) =
      ((F'.val.filter (fun z => ¬ b z = w)).map b.base).map (stalkClass W) := by
    rw [Multiset.map_map]
    refine Multiset.map_congr rfl fun z hz => ?_
    exact stalkClass_congr
      (nonempty_ringEquiv_stalk_blowUpToBase_of_ne w hwc z (Multiset.mem_filter.mp hz).2).some
  rw [h1]
  congr 1
  refine (Multiset.Nodup.ext ?_ (F.erase w).nodup).mpr fun y => ?_
  · exact Multiset.Nodup.map_on (fun z₁ hz₁ z₂ _ h =>
      blowUpToBase_injective_of_ne w hwc (Multiset.mem_filter.mp hz₁).2 h) (F'.nodup.filter _)
  · simp only [Multiset.mem_map, Multiset.mem_filter, Finset.mem_val, Finset.mem_erase, hF,
      hF', Set.Finite.mem_toFinset]
    constructor
    · rintro ⟨z, ⟨hz, hzw⟩, rfl⟩
      exact ⟨hzw, (mem_singularLocus_blowUp_iff_of_ne w hwc z hzw).mp hz⟩
    · rintro ⟨hyw, hy⟩
      obtain ⟨z, rfl⟩ := exists_blowUpToBase_eq_of_ne w hwc _ hyw
      exact ⟨z, ⟨(mem_singularLocus_blowUp_iff_of_ne w hwc z hyw).mpr hy, hyw⟩, rfl⟩

/-- If the classes of the singular local rings over the blown-up point are `≺`-smaller than the
class at that point, the multiset of classes of singular local rings decreases. -/
theorem cutExpand_stageMultiset_blowUp (hw : w ∈ singularLocus W)
    (hfin : (singularLocus W).Finite)
    (hfin' : (singularLocus
      (blowUp (Scheme.IdealSheafData.vanishingIdeal (⟨{w}, hwc⟩ : Closeds W)))).Finite)
    (hlt : ∀ z ∈ singularLocus
        (blowUp (Scheme.IdealSheafData.vanishingIdeal (⟨{w}, hwc⟩ : Closeds W))),
      blowUpToBase (Scheme.IdealSheafData.vanishingIdeal (⟨{w}, hwc⟩ : Closeds W)) z = w →
        BlowUpRelOption (stalkClass _ z) (stalkClass W w)) :
    Relation.CutExpand BlowUpRelOption
      (stageMultiset (blowUp (Scheme.IdealSheafData.vanishingIdeal (⟨{w}, hwc⟩ : Closeds W))))
      (stageMultiset W) := by
  classical
  have hoff := map_stalkClass_filter_ne_blowUp w hwc hfin hfin'
  set I := Scheme.IdealSheafData.vanishingIdeal (⟨{w}, hwc⟩ : Closeds W)
  set b := blowUpToBase I
  rw [stageMultiset, dite_eq_left hfin', stageMultiset, dite_eq_left hfin]
  set F := hfin.toFinset
  set F' := hfin'.toFinset
  refine ⟨(F'.val.filter (fun z => b z = w)).map (stalkClass (blowUp I)), stalkClass W w,
    ?_, ?_⟩
  · intro a ha
    obtain ⟨z, hz, rfl⟩ := Multiset.mem_map.mp ha
    obtain ⟨hzF, hzw⟩ := Multiset.mem_filter.mp hz
    exact hlt z (hfin'.mem_toFinset.mp hzF) hzw
  · have hsplitM : F'.val.map (stalkClass (blowUp I)) =
        (F'.val.filter (fun z => b z = w)).map (stalkClass (blowUp I)) +
          (F'.val.filter (fun z => ¬ b z = w)).map (stalkClass (blowUp I)) := by
      rw [← Multiset.map_add, Multiset.filter_add_not]
    have hdown : F.val.map (stalkClass W) =
        (F.erase w).val.map (stalkClass W) + {stalkClass W w} := by
      conv_lhs => rw [← Multiset.cons_erase (show w ∈ F.val from hfin.mem_toFinset.mpr hw)]
      rw [Finset.erase_val, Multiset.map_cons, add_comm, Multiset.singleton_add]
    rw [hsplitM, hoff, hdown]
    abel

end BlowUpOffCentre

/-- Blowing up a singular point of a stage gives a stage again. -/
theorem isRationalDoublePointStageNoetherian_blowUp
    (hL : RationalDoublePointBlowUpProperties.{u}) {W : Scheme.{u}}
    (hW : IsRationalDoublePointStageNoetherian W) (w : W) (hw : w ∈ singularLocus W)
    (hwc : IsClosed ({w} : Set W)) :
    IsRationalDoublePointStageNoetherian
      (blowUp (Scheme.IdealSheafData.vanishingIdeal (⟨{w}, hwc⟩ : Closeds W))) := by
  obtain ⟨hnoeth, ⟨hnorm, hfin, hrdp⟩, hclosed⟩ := hW
  have := hnoeth
  obtain ⟨T, ⟨eT⟩⟩ := hrdp w hw
  set I := Scheme.IdealSheafData.vanishingIdeal (⟨{w}, hwc⟩ : Closeds W)
  set b := blowUpToBase I
  obtain ⟨ψ, -, hψiso, -, hψsurj, hψclosed, -⟩ :=
    exists_hom_blowUp_maximalIdealSheaf_localization T.A w hwc eT
  obtain ⟨hLnorm, hLfin, hLsing⟩ := hL T
  let X := blowUp (maximalIdealSheaf T.A)
  have eoff := nonempty_ringEquiv_stalk_blowUpToBase_of_ne w hwc
  have hsing_off := mem_singularLocus_blowUp_iff_of_ne w hwc
  have eon : ∀ x : X, Nonempty ((blowUp I).presheaf.stalk (ψ x) ≃+* X.presheaf.stalk x) :=
    fun x => have := hψiso x; nonempty_ringEquiv_stalk_of_isIso_stalkMap ψ x
  have hsing_on : ∀ x : X, (ψ x ∈ singularLocus (blowUp I) ↔ x ∈ singularLocus X) :=
    fun x => have := hψiso x; mem_singularLocus_iff_of_isIso_stalkMap ψ x
  have hfin' : (singularLocus (blowUp I)).Finite := by
    refine ((Set.Finite.preimage (f := b.base)
      (fun z₁ hz₁ z₂ _ h => blowUpToBase_injective_of_ne w hwc hz₁.2 h)
        (hfin.sdiff : (singularLocus W \ {w}).Finite)).union
        (hLfin.image ψ.base)).subset fun z hz => ?_
    by_cases hzw : b z = w
    · obtain ⟨x, rfl⟩ := hψsurj z hzw
      exact Or.inr ⟨x, (hsing_on x).mp hz, rfl⟩
    · exact Or.inl ⟨(hsing_off z hzw).mp hz, hzw⟩
  refine ⟨Stacks.ResolutionOfSurfaces.isNoetherian_blowUp I, ⟨?_, hfin', fun z hz => ?_⟩,
    fun z hz => ?_⟩
  · refine (isNormal_iff_stalk_isNormalRing _).mpr fun z => ?_
    by_cases hzw : b z = w
    · obtain ⟨x, rfl⟩ := hψsurj z hzw
      exact IsNormalRing.congr (eon x).some.symm
        ((isNormal_iff_stalk_isNormalRing X).mp hLnorm x)
    · exact IsNormalRing.congr (eoff z hzw).some.symm
        ((isNormal_iff_stalk_isNormalRing W).mp hnorm (b z))
  · by_cases hzw : b z = w
    · obtain ⟨x, rfl⟩ := hψsurj z hzw
      obtain ⟨S, ⟨e⟩⟩ := (hLsing x ((hsing_on x).mp hz)).2.2
      exact ⟨S, ⟨e.trans (eon x).some.symm⟩⟩
    · obtain ⟨S, ⟨e⟩⟩ := hrdp (b z) ((hsing_off z hzw).mp hz)
      exact ⟨S, ⟨e.trans (eoff z hzw).some.symm⟩⟩
  · by_cases hzw : b z = w
    · obtain ⟨x, rfl⟩ := hψsurj z hzw
      have hx := (hsing_on x).mp hz
      exact (hψclosed x (hLsing x hx).2.1).mpr (hLsing x hx).1
    · exact isClosed_singleton_blowUp_of_ne w hwc hzw (hclosed _ ((hsing_off z hzw).mp hz))

/-- Blowing up a singular point of a stage decreases the multiset of classes of singular local
rings: the class at the blown-up point is replaced by the `≺`-smaller classes over it. -/
theorem cutExpand_stageMultiset_blowUp_of_stage
    (hL : RationalDoublePointBlowUpProperties.{u}) {W : Scheme.{u}}
    (hW : IsRationalDoublePointStageNoetherian W) (w : W) (hw : w ∈ singularLocus W)
    (hwc : IsClosed ({w} : Set W)) :
    Relation.CutExpand BlowUpRelOption
      (stageMultiset (blowUp (Scheme.IdealSheafData.vanishingIdeal (⟨{w}, hwc⟩ : Closeds W))))
      (stageMultiset W) := by
  have hfin' := (isRationalDoublePointStageNoetherian_blowUp hL hW w hw hwc).2.1.2.1
  obtain ⟨hnoeth, ⟨-, hfin, hrdp⟩, -⟩ := hW
  have := hnoeth
  obtain ⟨T, ⟨eT⟩⟩ := hrdp w hw
  obtain ⟨ψ, -, hψiso, -, hψsurj, -, -⟩ :=
    exists_hom_blowUp_maximalIdealSheaf_localization T.A w hwc eT
  obtain ⟨-, -, hLsing⟩ := hL T
  refine cutExpand_stageMultiset_blowUp w hwc hw hfin hfin' fun z hz hzw => ?_
  obtain ⟨x, rfl⟩ := hψsurj z hzw
  have := hψiso x
  let e' := (nonempty_ringEquiv_stalk_of_isIso_stalkMap ψ x).some
  have hx : x ∈ singularLocus (blowUp (maximalIdealSheaf T.A)) :=
    (mem_singularLocus_iff_of_isIso_stalkMap ψ x).mp hz
  obtain ⟨S, ⟨e⟩⟩ := (hLsing x hx).2.2
  rw [stalkClass_eq_some S (e.trans e'.symm), stalkClass_eq_some T eT]
  exact ⟨T, ⟨RingEquiv.refl _⟩, x, hx,
    ⟨(StacksDraft.exists_adicCompletion_ringEquiv_of_ringEquiv e).choose⟩⟩

/-- **One step of the induction.** Blowing up a singular point of a stage gives a stage again,
and the multiset of classes of singular local rings decreases: the class at the blown-up point is
replaced by the classes at the singular points over it, which are `≺`-smaller. -/
theorem IsRationalDoublePointStageNoetherian.blowUp_step
    (hL : RationalDoublePointBlowUpProperties.{u}) {W : Scheme.{u}}
    (hW : IsRationalDoublePointStageNoetherian W) (w : W) (hw : w ∈ singularLocus W)
    (hwc : IsClosed ({w} : Set W)) :
    IsRationalDoublePointStageNoetherian
        (blowUp (Scheme.IdealSheafData.vanishingIdeal (⟨{w}, hwc⟩ : Closeds W))) ∧
      Relation.CutExpand BlowUpRelOption
        (stageMultiset (blowUp (Scheme.IdealSheafData.vanishingIdeal (⟨{w}, hwc⟩ : Closeds W))))
        (stageMultiset W) :=
  ⟨isRationalDoublePointStageNoetherian_blowUp hL hW w hw hwc,
    cutExpand_stageMultiset_blowUp_of_stage hL hW w hw hwc⟩

/-- **The assembly.** Granted the local information on the blowup of a rational double point in
its maximal ideal and the well-foundedness of `≺`, every stage is resolved by a finite sequence of
blowups in singular closed points through stages. -/
theorem exists_singularPointBlowupChain_isRegular_of_blowUpRel
    (hL : RationalDoublePointBlowUpProperties.{u}) (hwf : WellFounded BlowUpRel.{u})
    (X : Scheme.{u}) (hX : IsRationalDoublePointStageNoetherian X) :
    ∃ (Y : Scheme.{u}) (f : Y ⟶ X),
      SingularPointBlowupChain IsRationalDoublePointStageNoetherian X Y f ∧ IsRegular Y := by
  classical
  refine exists_singularPointBlowupChain_isRegular_of_wellFounded
    (wellFounded_blowUpRelOption hwf) IsRationalDoublePointStageNoetherian stageMultiset
    ?_ ?_ X hX
  · intro W hW hM
    obtain ⟨hnoeth, ⟨-, hfin, -⟩, -⟩ := hW
    have := hnoeth
    rw [stageMultiset, dite_eq_left hfin, Multiset.map_eq_zero, Finset.val_eq_zero,
      Set.Finite.toFinset_eq_empty] at hM
    exact isRegular_of_singularLocus_eq_empty W hM
  · intro W hW hM
    obtain ⟨w, hw⟩ : (singularLocus W).Nonempty := by
      by_contra! hne
      apply hM
      rw [stageMultiset, dite_eq_left (hne ▸ Set.finite_empty)]
      simp [hne]
    have hwc := hW.2.2 w hw
    exact ⟨w, hwc, hw, hW.blowUp_step hL w hw hwc⟩

/-- A closed point of a scheme proper over the spectrum of a local ring lies over the closed
point. -/
theorem apply_eq_closedPoint_of_isClosed_of_isProper {A : Type u} [CommRing A] [IsLocalRing A]
    {Y : Scheme.{u}} (f : Y ⟶ Spec (.of A)) [IsProper f] (y : Y)
    (hy : IsClosed ({y} : Set Y)) : f y = closedPoint A := by
  have hc : IsClosed ({f y} : Set (Spec (.of A))) := by
    rw [← Set.image_singleton]
    exact f.isClosedMap _ hy
  exact PrimeSpectrum.ext <|
    IsLocalRing.eq_maximalIdeal ((PrimeSpectrum.isClosed_singleton_iff_isMaximal _).mp hc)

/-- **A chain of blowups in singular closed points with normal Noetherian stages, over the
spectrum of a local ring, is a chain of normalized blowups at closed points over the closed
point.** Every stage is normal, so blowing up and blowing up then normalizing agree up to the
normalization isomorphism; every stage is proper over the base, so its closed points lie over the
closed point. -/
theorem SingularPointBlowupChain.factorsAsNormalizedPointBlowups {A : Type u} [CommRing A]
    [IsLocalRing A] {Y : Scheme.{u}} {f : Y ⟶ Spec (.of A)}
    (h : SingularPointBlowupChain IsRationalDoublePointStageNoetherian (Spec (.of A)) Y f) :
    IsProper f ∧ Stacks.ResolutionOfSurfaces.FactorsAsNormalizedPointBlowups (Spec (.of A))
      {closedPoint A} Y f := by
  induction h with
  | refl hX =>
    exact ⟨inferInstance, Stacks.ResolutionOfSurfaces.FactorsAsNormalizedPointBlowups.refl _⟩
  | @step W g hh w hw hsing hP ih =>
    obtain ⟨hgp, hfac⟩ := ih
    have := hgp
    have : IsNoetherian W := hh.last.1
    have hZ : ∀ U : W.Opens, IsCompact (U : Set W) → (irreducibleComponents U).Finite := by
      intro U hU
      have : IsNoetherian U :=
        { toIsLocallyNoetherian := inferInstance
          toCompactSpace := isCompact_iff_compactSpace.mp hU }
      exact finite_irreducibleComponents_of_isNoetherian
    have : IsNormal (blowUp (Scheme.IdealSheafData.vanishingIdeal (⟨{w}, hw⟩ : Closeds W))) :=
      hP.2.1.1
    have := Scheme.isIso_normalization_of_isNormal
      (blowUp (Scheme.IdealSheafData.vanishingIdeal (⟨{w}, hw⟩ : Closeds W)))
      (Stacks.Blowup.finite_irreducibleComponents_blowUp _ hZ)
    refine ⟨inferInstance, ?_⟩
    refine ((hfac.step hZ w hw (apply_eq_closedPoint_of_isClosed_of_isProper g w hw)).of_iso
      (asIso (Scheme.normalization
      (blowUp (Scheme.IdealSheafData.vanishingIdeal (⟨{w}, hw⟩ : Closeds W)))
      (Stacks.Blowup.finite_irreducibleComponents_blowUp _ hZ))).symm).congr ?_
    simp [Stacks.Blowup.normalizedBlowUp]

/-- The spectrum of a two-dimensional local normal Nagata domain defining a rational singularity,
with normal completion, which is Gorenstein, is a stage. -/
theorem isRationalDoublePointStageNoetherian_spec (A : Type u) [CommRing A] [IsLocalRing A]
    [IsNormalDomain A] (hN : IsNagataRing A) (hdim : ringKrullDim A = 2)
    (hrat : DefinesRationalSingularity A)
    (hcompl : IsNormalRing (AdicCompletion (maximalIdeal A) A))
    (hgor : letI := hN.1; Dualizing.IsGorensteinLocalRing A) :
    IsRationalDoublePointStageNoetherian (Spec (.of A)) := by
  have : IsNoetherianRing A := hN.1
  have hcd : IsNormalDomain (AdicCompletion (maximalIdeal A) A) := by
    obtain ⟨hD, hIC⟩ := hcompl.of_isLocalRing
    exact ⟨hD, hIC⟩
  obtain ⟨hnorm, hfin, -, hsit⟩ :=
    isNormal_and_finite_singularLocus_and_exists_situation A hN hdim hrat hcd hgor
  refine ⟨inferInstance, ⟨hnorm, hfin, hsit⟩, fun y hy => ?_⟩
  rw [singularLocus_spec_subset_closedPoint A hdim hy]
  exact IsLocalRing.isClosed_singleton_closedPoint A

/-- **[Stacks, Tag 0BGE] from the local information.** Granted the properties of the blowup of a
rational double point in its maximal ideal and the well-foundedness of `≺`, the spectrum of a
two-dimensional local normal Nagata domain defining a rational singularity, with normal
completion, which is Gorenstein, is resolved by a finite sequence of blowups in singular closed
points, every stage being normal with finitely many singular points, each a rational double
point; and that sequence is a sequence of normalized blowups at closed points over the closed
point. -/
theorem exists_chains_isRegular_of_blowUpProperties
    (hL : RationalDoublePointBlowUpProperties.{u}) (hwf : WellFounded BlowUpRel.{u})
    (A : Type u) [CommRing A] [IsLocalRing A] [IsNormalDomain A] (hN : IsNagataRing A)
    (hdim : ringKrullDim A = 2) (hrat : DefinesRationalSingularity A)
    (hcompl : IsNormalRing (AdicCompletion (maximalIdeal A) A))
    (hgor : letI := hN.1; Dualizing.IsGorensteinLocalRing A) :
    ∃ (Y : Scheme.{u}) (f : Y ⟶ Spec (.of A)),
      SingularPointBlowupChain IsRationalDoublePointStageNoetherian (Spec (.of A)) Y f ∧
        IsRegular Y :=
  exists_singularPointBlowupChain_isRegular_of_blowUpRel hL hwf _
    (isRationalDoublePointStageNoetherian_spec A hN hdim hrat hcompl hgor)

end AlgebraicGeometry

end
