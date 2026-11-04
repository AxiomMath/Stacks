module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.FiniteLocallyConstantLimitCategory
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.StalkLocus
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FinitePushforwardBaseChange
public import StacksFrontier.AlgebraicGeometry.Limits.Descending.ConstructibleImage
public import StacksCore.Tactic.StacksAttribute

/-!
# Maps of constructible sheaves of sets on a limit of schemes are detected at a finite stage

Let `X = lim X_i` be the limit of a directed inverse system of quasi-compact and quasi-separated
schemes with affine transition morphisms. Two maps of constructible sheaves of sets on
`(X_i)_étale` whose inverse images to `X_étale` agree already agree after inverse image to some
later stage. This is the faithfulness assertion of Tag 09YU, clause (1).

The argument is the one of the source. The locus in `X_i` where the two maps induce the same map
of geometric stalks is the locus where the geometric stalk of the inclusion of their equalizer is
surjective, because the geometric stalk functor is left exact; that equalizer is constructible,
being a finite limit of constructible sheaves, so the locus is constructible by Tag 09YS. It
contains the image of `X`, hence by Tag 05F4 the image of every sufficiently late stage, and at
such a stage the inverse image of the equalizer inclusion is an isomorphism on every geometric
stalk, hence an isomorphism by Tag 03PU, and the two inverse images agree.

## Main definitions

* `AlgebraicGeometry.descentSituationOfBigEtaleCone` — a limiting cone over an inverse system of
  quasi-compact, quasi-separated schemes with affine transitions inside a big étale site, read as
  the descent situation of Tag 09RD.

## Main results

* `AlgebraicGeometry.surjective_etaleStalk_map_iff_of_base_eq` — surjectivity of the geometric
  stalk map of a morphism of sheaves of sets does not depend on the geometric point chosen above
  a point of the scheme.
* `AlgebraicGeometry.surjective_etaleStalk_map_fork_ι_iff` and
  `AlgebraicGeometry.injective_etaleStalk_map_fork_ι` — the geometric stalk of the inclusion of
  the equalizer of two maps of sheaves of sets is always injective, and is surjective exactly
  where the two maps have the same geometric stalk.
* `AlgebraicGeometry.etaleStalk_map_eq_of_smallEtaleSheafPullback_map_eq` and
  `AlgebraicGeometry.isIso_etaleStalk_map_smallEtaleSheafPullback` — transport of equality and of
  invertibility of geometric stalk maps along inverse image.
* `AlgebraicGeometry.smallEtaleStagesFaithful_isConstructibleSetSheaf` — **Tag 09YU, clause (1),
  the faithfulness assertion.**

## Implementation notes

The equalizer-based statements are phrased for an arbitrary limit fork rather than for
`CategoryTheory.Limits.equalizer`, so that the instance providing equalizers of sheaves of sets —
which carries a coefficient universe not determined by the statement — does not have to be
resolved while elaborating them.

The stalk at a geometric point is used in the spelling
`CategoryTheory.GrothendieckTopology.Point.sheafFiber` of the point
`AlgebraicGeometry.geometricPointSitePoint`, which is the spelling the left exactness of the
stalk comes in; by `AlgebraicGeometry.etaleStalk_eq_presheafFiber` it is the same functor as
`AlgebraicGeometry.etaleStalkPresheafFunctor`, in which Tag 09YS is stated.

Only the faithfulness assertion of Tag 09YU is proved. Its fullness and essential surjectivity
assertions reduce in the source to Tag 09Y9 and Theorem Tag 09YQ.

## References

* [Stacks Project, Tag 09YU](https://stacks.math.columbia.edu/tag/09YU)
* [Stacks Project, Tag 09YS](https://stacks.math.columbia.edu/tag/09YS)
* [Stacks Project, Tag 05F4](https://stacks.math.columbia.edu/tag/05F4)
* [Stacks Project, Tag 03PU](https://stacks.math.columbia.edu/tag/03PU)
* [Stacks Project, Tag 09RD](https://stacks.math.columbia.edu/tag/09RD)
* [Stacks Project, Tag 03RZ](https://stacks.math.columbia.edu/tag/03RZ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Filter

universe u

namespace AlgebraicGeometry

section Stalk

variable (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- Surjectivity of the map induced on a geometric stalk by a morphism of sheaves of sets does
not depend on the geometric point chosen above a given point of the scheme. -/
public theorem surjective_etaleStalk_map_iff_of_base_eq
    {F G : Sheaf (SmallEtale.topology B S hS) (Type (u + 1))} (φ : F ⟶ G)
    {p q : GeometricPoint S} (h : p.hom default = q.hom default) :
    Function.Surjective (ConcreteCategory.hom
        (((geometricPointSitePoint B S hS p).sheafFiber (A := Type (u + 1))).map φ)) ↔
      Function.Surjective (ConcreteCategory.hom
        (((geometricPointSitePoint B S hS q).sheafFiber (A := Type (u + 1))).map φ)) :=
  property_etaleStalk_map_iff_of_base_eq B S hS φ (fun _ _ m => Function.Surjective m)
    (fun _ _ _ _ g g' e₁ e₂ he => by
      have hg' : g' = ⇑e₂ ∘ g ∘ ⇑e₁.symm := funext fun w => by simpa using (he (e₁.symm w)).symm
      rw [hg', Equiv.comp_surjective, Equiv.surjective_comp]) h

variable {K F G : Sheaf (SmallEtale.topology B S hS) (Type (u + 1))}

/-- **The equalizer of two maps of sheaves of sets is detected on the geometric stalks.** The map
induced on a geometric stalk by the inclusion of a limit fork of two morphisms of sheaves of sets
is surjective exactly when the two morphisms induce the same map on that stalk. -/
public theorem surjective_etaleStalk_map_fork_ι_iff (a b : F ⟶ G) (m : K ⟶ F)
    (w : m ≫ a = m ≫ b) (hm : IsLimit (Fork.ofι m w)) (t : GeometricPoint S) :
    Function.Surjective (ConcreteCategory.hom
        (((geometricPointSitePoint B S hS t).sheafFiber (A := Type (u + 1))).map m)) ↔
      ((geometricPointSitePoint B S hS t).sheafFiber (A := Type (u + 1))).map a =
        ((geometricPointSitePoint B S hS t).sheafFiber (A := Type (u + 1))).map b := by
  have hAB : AB5OfSize.{u, u} (Type (u + 1)) := AB5OfSize_of_univLE.{u, u, u + 1, u + 1} _
  set Φ := (geometricPointSitePoint B S hS t).sheafFiber (A := Type (u + 1))
  have hcomm : Φ.map m ≫ Φ.map a = Φ.map m ≫ Φ.map b := by
    rw [← Φ.map_comp, ← Φ.map_comp, w]
  constructor
  · intro hsurj
    refine ConcreteCategory.hom_ext _ _ fun y => ?_
    obtain ⟨z, hz⟩ := hsurj y
    simpa only [ConcreteCategory.comp_apply, hz] using ConcreteCategory.congr_hom hcomm z
  · intro heq
    obtain ⟨l, hl'⟩ := Fork.IsLimit.lift' (isLimitForkMapOfIsLimit Φ w hm) (𝟙 (Φ.obj F))
      (by rw [Category.id_comp, Category.id_comp, heq])
    intro y
    exact ⟨ConcreteCategory.hom l y, by
      simpa [ConcreteCategory.comp_apply] using ConcreteCategory.congr_hom hl' y⟩

/-- The map induced on a geometric stalk by the inclusion of a limit fork of two morphisms of
sheaves of sets is injective: the geometric stalk functor is left exact, so it carries that
inclusion to a limit fork again. -/
public theorem injective_etaleStalk_map_fork_ι (a b : F ⟶ G) (m : K ⟶ F)
    (w : m ≫ a = m ≫ b) (hm : IsLimit (Fork.ofι m w)) (t : GeometricPoint S) :
    Function.Injective (ConcreteCategory.hom
      (((geometricPointSitePoint B S hS t).sheafFiber (A := Type (u + 1))).map m)) := by
  have hAB : AB5OfSize.{u, u} (Type (u + 1)) := AB5OfSize_of_univLE.{u, u, u + 1, u + 1} _
  set Φ := (geometricPointSitePoint B S hS t).sheafFiber (A := Type (u + 1))
  rw [← CategoryTheory.mono_iff_injective]
  exact mono_of_isLimit_fork (isLimitForkMapOfIsLimit Φ w hm)

end Stalk

section Pullback

variable (B : BigEtaleSite.{u}) {S T : B.Scheme} (f : T ⟶ S) (x : GeometricPoint T.obj)

/-- Two morphisms of sheaves of sets whose inverse images along a morphism of a big étale site
agree induce the same map on the geometric stalk at the image of any geometric point of the
source. -/
public theorem etaleStalk_map_eq_of_smallEtaleSheafPullback_map_eq
    {F G : Sheaf (SmallEtale.topology B S.obj S.property) (Type (u + 1))} (a b : F ⟶ G)
    (h : (smallEtaleSheafPullback B (Type (u + 1)) f).map a =
      (smallEtaleSheafPullback B (Type (u + 1)) f).map b) :
    ((geometricPointSitePoint B S.obj S.property
          (x.map (B.inclusion.map f))).sheafFiber (A := Type (u + 1))).map a =
      ((geometricPointSitePoint B S.obj S.property
          (x.map (B.inclusion.map f))).sheafFiber (A := Type (u + 1))).map b := by
  have e := smallEtalePullbackSheafFiberIso B f x (Type (u + 1))
  have hna := e.hom.naturality a
  have hnb := e.hom.naturality b
  simp only [Functor.comp_map] at hna hnb
  rw [h, hnb] at hna
  exact ((cancel_epi (e.hom.app F)).mp hna).symm

/-- A morphism of sheaves of sets which induces an isomorphism on the geometric stalk at the
image of a geometric point induces an isomorphism on the geometric stalk of its inverse image at
that geometric point. -/
public theorem isIso_etaleStalk_map_smallEtaleSheafPullback
    {E F : Sheaf (SmallEtale.topology B S.obj S.property) (Type (u + 1))} (φ : E ⟶ F)
    (h : IsIso (((geometricPointSitePoint B S.obj S.property
      (x.map (B.inclusion.map f))).sheafFiber (A := Type (u + 1))).map φ)) :
    IsIso (((geometricPointSitePoint B T.obj T.property x).sheafFiber
      (A := Type (u + 1))).map ((smallEtaleSheafPullback B (Type (u + 1)) f).map φ)) := by
  have e := smallEtalePullbackSheafFiberIso B f x (Type (u + 1))
  have hn := e.hom.naturality φ
  have hrw : ((geometricPointSitePoint B T.obj T.property x).sheafFiber
        (A := Type (u + 1))).map ((smallEtaleSheafPullback B (Type (u + 1)) f).map φ) =
      e.hom.app E ≫ (((geometricPointSitePoint B S.obj S.property
        (x.map (B.inclusion.map f))).sheafFiber (A := Type (u + 1))).map φ) ≫
          inv (e.hom.app F) := by
    rw [← Category.assoc, ← hn]
    simp
  rw [hrw]
  infer_instance

end Pullback

section Descent

variable (B : BigEtaleSite.{u}) {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]
  (Dg : Iᵒᵖ ⥤ B.Scheme) (c : Cone (Dg ⋙ B.inclusion))

/-- **The descent situation of Tag 09RD attached to a cone in a big étale site.** A limiting cone
over an inverse system of quasi-compact, quasi-separated schemes with affine transition morphisms
inside a big étale site, read as a directed inverse system of schemes with a chosen index. -/
public def descentSituationOfBigEtaleCone (hc : IsLimit c)
    (haff : ∀ {p q : Iᵒᵖ} (e : p ⟶ q), IsAffineHom (B.inclusion.map (Dg.map e)))
    (hqc : ∀ p : I, CompactSpace (Dg.obj (op p)).obj)
    (hqs : ∀ p : I, QuasiSeparatedSpace (Dg.obj (op p)).obj) (i : I) :
    DescentSituation.{u, u} I where
  system := Dg ⋙ B.inclusion
  transition_affine e := haff e
  quasiCompact p := hqc p
  quasiSeparated p := hqs p
  limitCone := c
  isLimit := hc
  base := i

variable (hX : B.Contains c.pt)

/-- **Stacks 09YU, clause (1), the faithfulness assertion.** Let `X = lim X_i` be the limit of a
directed inverse system of quasi-compact and quasi-separated schemes with affine transition
morphisms. Two maps of constructible sheaves of sets on `(X_i)_étale` whose inverse images to
`X_étale` agree agree after inverse image to some later stage.

The locus in `X_i` where the two maps have the same geometric stalk is the locus where the
geometric stalk of the inclusion of their equalizer is surjective; the equalizer is constructible
by Tag 03RZ, so that locus is constructible by Tag 09YS and contains the image of `X`, hence by
Tag 05F4 the image of a later stage, where Tag 03PU turns the inverse image of the inclusion into
an isomorphism. -/
@[stacks 09YU "clause (1), the faithfulness assertion"]
public theorem smallEtaleStagesFaithful_isConstructibleSetSheaf (hc : IsLimit c)
    (haff : ∀ {p q : Iᵒᵖ} (e : p ⟶ q), IsAffineHom (B.inclusion.map (Dg.map e)))
    (hqc : ∀ p : I, CompactSpace (Dg.obj (op p)).obj)
    (hqs : ∀ p : I, QuasiSeparatedSpace (Dg.obj (op p)).obj) :
    SmallEtaleStagesFaithful B (Type (u + 1)) Dg c hX
      (fun Y => IsConstructibleSetSheaf B Y) := by
  intro i F G hF hG a b hab
  have : Nonempty I := ⟨i⟩
  have : CompactSpace (Dg.obj (op i)).obj := hqc i
  have : QuasiSeparatedSpace (Dg.obj (op i)).obj := hqs i
  have : HasLimitsOfShape WalkingParallelPair
      (Sheaf (SmallEtale.topology B (Dg.obj (op i)).obj (Dg.obj (op i)).property)
        (Type (u + 1))) := HasFiniteLimits.out _
  have hw : equalizer.ι a b ≫ a = equalizer.ι a b ≫ b := equalizer.condition a b
  have hm : IsLimit (Fork.ofι (equalizer.ι a b) hw) := equalizerIsEqualizer a b
  have hE : IsConstructibleSetSheaf B (Dg.obj (op i)) (equalizer a b) :=
    isConstructibleSetSheaf_limit B _ (parallelPair a b) (by rintro (_ | _) <;> assumption)
  set L := {y : (Dg.obj (op i)).obj | ∃ t : GeometricPoint (Dg.obj (op i)).obj, t.LiesOver y ∧
    Function.Surjective (ConcreteCategory.hom
      (((geometricPointSitePoint B (Dg.obj (op i)).obj (Dg.obj (op i)).property t).sheafFiber
        (A := Type (u + 1))).map (equalizer.ι a b)))}
  have hLc : Topology.IsConstructible L :=
    isConstructible_setOf_surjective_etaleStalk_map B _ (equalizer.ι a b) hE hF
  set p : B.obj c.pt hX ⟶ Dg.obj (op i) := ObjectProperty.homMk (c.π.app (op i))
  have hpi : B.inclusion.map p = c.π.app (op i) := rfl
  have hlim : Set.range ⇑(c.π.app (op i)) ⊆ L := by
    rintro y ⟨y', rfl⟩
    refine ⟨(GeometricPoint.ofPoint c.pt y').map (B.inclusion.map p), ?_, ?_⟩
    · simp only [GeometricPoint.LiesOver, GeometricPoint.map_hom, hpi]
      simp
    · exact (surjective_etaleStalk_map_fork_ι_iff B _ _ a b _ hw hm _).mpr
        (etaleStalk_map_eq_of_smallEtaleSheafPullback_map_eq B p
          (GeometricPoint.ofPoint c.pt y') a b hab)
  obtain ⟨j₀, hj₀⟩ := eventually_atTop.mp
    (eventually_range_transition_subset_of_isLocallyConstructible
      (descentSituationOfBigEtaleCone B Dg c hc haff hqc hqs i) L
      hLc.isLocallyConstructible hlim)
  obtain ⟨j, hij, hj₀j⟩ := directed_of (· ≤ ·) i j₀
  obtain ⟨hbj, hsub⟩ := hj₀ j hj₀j
  refine ⟨j, hij, ?_⟩
  have hiso : IsIso ((smallEtaleStageTransition B (Type (u + 1)) Dg hij).map
      (equalizer.ι a b)) := by
    refine isIso_of_bijective_etaleStalkMap B (Dg.obj (op j)).obj (Dg.obj (op j)).property
      _ fun s => ?_
    have hmem : (B.inclusion.map (Dg.map (homOfLE hij).op)).base (s.hom.base default) ∈ L :=
      hsub ⟨s.hom.base default, rfl⟩
    obtain ⟨t, htb, hts⟩ := hmem
    have hbase : (s.map (B.inclusion.map (Dg.map (homOfLE hij).op))).hom.base default =
        t.hom.base default := by
      simp only [GeometricPoint.map_hom]
      simpa using htb.symm
    have hsurj := (surjective_etaleStalk_map_iff_of_base_eq B (Dg.obj (op i)).obj
      (Dg.obj (op i)).property (equalizer.ι a b) hbase).mpr hts
    have hinj := injective_etaleStalk_map_fork_ι B (Dg.obj (op i)).obj
      (Dg.obj (op i)).property a b (equalizer.ι a b) hw hm
      (s.map (B.inclusion.map (Dg.map (homOfLE hij).op)))
    have hbij : IsIso ((((geometricPointSitePoint B (Dg.obj (op i)).obj
        (Dg.obj (op i)).property
          (s.map (B.inclusion.map (Dg.map (homOfLE hij).op)))).sheafFiber
          (A := Type (u + 1)))).map (equalizer.ι a b)) := by
      rw [ConcreteCategory.isIso_iff_bijective]
      exact ⟨hinj, hsurj⟩
    rw [← ConcreteCategory.isIso_iff_bijective]
    exact isIso_etaleStalk_map_smallEtaleSheafPullback B (Dg.map (homOfLE hij).op) s
      (equalizer.ι a b) hbij
  have hcond := congrArg (smallEtaleStageTransition B (Type (u + 1)) Dg hij).map hw
  rw [Functor.map_comp, Functor.map_comp] at hcond
  exact (cancel_epi _).mp hcond

end Descent

end AlgebraicGeometry

end
