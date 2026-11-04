module

public import StacksFrontier.AlgebraicGeometry.Full.Square
public import StacksFrontier.AlgebraicGeometry.FullyFaithful.Basic

/-!
# Fullness of the canonical restriction functor near finitely many closed points

Let `S` be a scheme, let `s : I → S` be a finite family of *distinct* closed points, write
`U = S \ {s i | i}` for the open complement and assume `U ⟶ S` is quasi-compact.
[Stacks, Tag 0E8Q](https://stacks.math.columbia.edu/tag/0E8Q) asserts that the canonical
functor `AlgebraicGeometry.canonicalRestrictionFunctor` from schemes of finite presentation
over `S` to gluing data is an equivalence, and omits the proof of full faithfulness.  The
faithful half is `AlgebraicGeometry.faithful_canonicalRestrictionFunctor`; this file proves the
**full** half.

The mechanism is again fpqc descent along the covering family of
`AlgebraicGeometry.LocalSchemesCover.presieve₀_mem_fpqcPrecoverage`, but now in its
*amalgamation* direction rather than its separatedness direction.  Base changed to the source
`X` of the morphism being constructed, the family becomes `X ×_S U ⟶ X` together with the
`X ×_S S_i ⟶ X`, and a morphism of gluing data supplies a morphism to `Y` on each member.  The
sheaf condition for `yoneda.obj Y` then produces the unique morphism `X ⟶ Y` restricting to all
of them, which is exactly a preimage of the given morphism of gluing data.

What has to be checked is the compatibility of that family on overlaps, and the four cases are
genuinely different:

* the overlap of the open member with itself, and of a local member with itself, carry no
  condition at all, because every member of the family is a *monomorphism* — an open immersion
  in the first case, and `AlgebraicGeometry.Scheme.fromSpecStalk`, which is a preimmersion, in
  the second;
* the overlap of the open member with the local member at `s i` is the punctured local scheme
  `U_i`, and there the compatibility *is* the commutative square that a morphism of gluing data
  carries, transported across the base-change comparison isomorphism by
  `CategoryTheory.Over.pullbackSquare_fst_comp_left`;
* the overlap of two *distinct* local members lies over `U`, by
  `AlgebraicGeometry.LocalSchemesCover.specializes_mem_complement`, so it factors through the
  open member and its compatibility is deduced from the previous case twice.  (The set-level
  form of that containment is
  `AlgebraicGeometry.LocalSchemesCover.range_inter_range_subset`, but the factorization needs
  membership for one point at a time, so the lemma below it is the usable one.)

The third bullet is where the injectivity of the family of points enters, and it is the only
place: `AlgebraicGeometry.LocalSchemesCover.exists_lift_complement_of_ne` turns the set-level
containment of images into a factorization of schemes, using
`AlgebraicGeometry.IsOpenImmersion.lift`.

## Main results

* `AlgebraicGeometry.LocalSchemesCover.exists_lift_complement_of_ne`: a scheme mapping to `S`
  through two *distinct* local schemes of the family maps through the open complement.
* `AlgebraicGeometry.LocalSchemesCover.exists_lift_puncturedLocalScheme`: a morphism to the
  local scheme at `s i` whose image in `S` lies in the open complement factors through the
  punctured local scheme.
* `AlgebraicGeometry.exists_over_hom_of_baseChange`: the amalgamation itself, for *arbitrary*
  objects of `Over S`.
* `AlgebraicGeometry.full_canonicalRestrictionFunctor`: the canonical restriction functor of
  Tag 0E8Q is full.
* `AlgebraicGeometry.fullyFaithfulCanonicalRestrictionFunctor`: it is fully faithful.

## Implementation notes

The descent argument is carried out in the `Descent` section for arbitrary objects `A B : Over S`
and a descent datum for morphisms given as raw data — a morphism of the base changes to the open
complement, a family of morphisms of the base changes to the local schemes, and the compatibility
`AlgebraicGeometry.PuncturedCompatible` over the punctured local schemes.  The finite
presentation carried by the objects of `canonicalRestrictionFunctor`'s source is never used: the
sheaf condition is applied to the base change of the covering family along `A.hom`, which is a
covering family for every morphism to `S`.  The `Full` section is the specialization to the datum
extracted from a morphism of gluing data, so `AlgebraicGeometry.openComponentLeft` and the lemmas
about it read the general statements at those components, and the amalgamation itself remains
available for objects of `Over S` which are not of finite presentation.

No tag is attached.  Tag 0E8Q's third label asserts that the canonical restriction functor is
an *equivalence*, and the covering set of that label is the single `IsEquivalence` assertion; a
fully faithful functor is not yet an equivalence, so this earns no partial credit on its own.
Essential surjectivity is [Stacks, Tag 0BPA](https://stacks.math.columbia.edu/tag/0BPA) and is
not proved here.

The two purely categorical steps of the overlap computation are isolated in
`StacksFrontier.AlgebraicGeometry.Full.Square`, which knows nothing about schemes: they
are statements about the base-change comparison isomorphism of a commutative square in any
category with pullbacks.

## References

* [Stacks Project, Tag 0E8Q](https://stacks.math.columbia.edu/tag/0E8Q)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Topology

universe u

namespace AlgebraicGeometry

namespace LocalSchemesCover

variable {S : Scheme.{u}} {I : Type u} [Finite I] (s : I → S)
  (hs : ∀ i, s i ∈ closedPoints S)

/-- Every member of the covering family is a monomorphism: the open complement is an open
immersion, and the canonical morphism from the spectrum of a local ring is a preimmersion. -/
instance mono_map (a : Option I) : Mono (map s hs a) := by
  cases a with
  | none => exact inferInstanceAs (Mono (complementOfClosedPoints s hs).ι)
  | some i => exact inferInstanceAs (Mono (S.fromSpecStalk (s i)))

/-- A morphism to `S` whose image lies in the open complement factors through the open
complement. -/
theorem exists_lift_complement {Z : Scheme.{u}} (z : Z ⟶ S)
    (hz : Set.range z.base ⊆ (complementOfClosedPoints s hs : Set S)) :
    ∃ c : Z ⟶ (complementOfClosedPoints s hs).toScheme,
      c ≫ (complementOfClosedPoints s hs).ι = z :=
  ⟨IsOpenImmersion.lift _ z (by rwa [Scheme.Opens.range_ι]), IsOpenImmersion.lift_fac _ _ _⟩

include hs in
/-- **A scheme mapping to `S` through the local schemes at two distinct points of the family
maps through the open complement.**  Its image lies in the intersection of the images of the two
local schemes, hence in the open complement by
`AlgebraicGeometry.LocalSchemesCover.specializes_mem_complement`, and the open complement is an
open immersion, so the factorization exists on schemes and not merely on points. -/
theorem exists_lift_complement_of_ne (hinj : Function.Injective s) {i j : I} (hij : i ≠ j)
    {Z : Scheme.{u}} {z : Z ⟶ S} {bi : Z ⟶ Spec (S.presheaf.stalk (s i))}
    {bj : Z ⟶ Spec (S.presheaf.stalk (s j))}
    (hbi : bi ≫ S.fromSpecStalk (s i) = z) (hbj : bj ≫ S.fromSpecStalk (s j) = z) :
    ∃ c : Z ⟶ (complementOfClosedPoints s hs).toScheme,
      c ≫ (complementOfClosedPoints s hs).ι = z := by
  refine exists_lift_complement s hs z fun y hy ↦ ?_
  obtain ⟨w, rfl⟩ := hy
  refine specializes_mem_complement s hs (fun e ↦ hij (hinj e)) ?_ ?_
  · rw [← hbi]
    exact (Scheme.range_fromSpecStalk (x := s i)).le ⟨bi.base w, rfl⟩
  · rw [← hbj]
    exact (Scheme.range_fromSpecStalk (x := s j)).le ⟨bj.base w, rfl⟩

/-- A morphism to the local scheme at `s i` whose image in `S` lies in the open complement
factors through the punctured local scheme. -/
theorem exists_lift_puncturedLocalScheme (i : I) {Z : Scheme.{u}}
    (b : Z ⟶ Spec (S.presheaf.stalk (s i)))
    (hb : Set.range (b ≫ S.fromSpecStalk (s i)).base ⊆
      (complementOfClosedPoints s hs : Set S)) :
    ∃ b' : Z ⟶ puncturedLocalScheme s hs i,
      b' ≫ ((S.fromSpecStalk (s i)) ⁻¹ᵁ (complementOfClosedPoints s hs)).ι = b := by
  refine ⟨IsOpenImmersion.lift _ b ?_, IsOpenImmersion.lift_fac _ _ _⟩
  rw [Scheme.Opens.range_ι]
  rintro _ ⟨w, rfl⟩
  exact hb ⟨w, rfl⟩

end LocalSchemesCover

/-- If a morphism between base changes along `t` is compatible with the projections to the
base of the base change, then its composite with the first projection is a morphism over `S`. -/
private theorem fst_comp_hom_of_comp_snd {S T X Y : Scheme.{u}} {a : X ⟶ S} {b : Y ⟶ S}
    {t : T ⟶ S} (f : pullback a t ⟶ pullback b t) (hf : f ≫ pullback.snd b t = pullback.snd a t) :
    (f ≫ pullback.fst b t) ≫ b = pullback.fst a t ≫ a := by
  rw [Category.assoc, pullback.condition, ← Category.assoc, hf, ← pullback.condition]

section Descent

variable {S : Scheme.{u}} {I : Type u} [Finite I] (s : I → S)
  (hs : ∀ i, s i ∈ closedPoints S) {A B : Over S}
  (gU : (Over.pullback (complementOfClosedPoints s hs).ι).obj A ⟶
    (Over.pullback (complementOfClosedPoints s hs).ι).obj B)
  (gL : ∀ i, (Over.pullback (S.fromSpecStalk (s i))).obj A ⟶
    (Over.pullback (S.fromSpecStalk (s i))).obj B)

/-- **Compatibility over the punctured local scheme at `s i` of a descent datum for
morphisms.**  A morphism `gU` between the base changes of `A` and `B` to the open complement and
a morphism `gL i` between their base changes to the local scheme at `s i` are compatible when
their further base changes to the punctured local scheme agree through the comparison
isomorphism `CategoryTheory.Over.pullbackSquareObjIso` of the square
`U_i ⟶ U ⟶ S = U_i ⟶ S_i ⟶ S`.  For the components of a morphism of gluing data this holds by
`AlgebraicGeometry.gluingData_square`. -/
abbrev PuncturedCompatible (i : I) : Prop :=
  (Over.pullback ((S.fromSpecStalk (s i)) ∣_ (complementOfClosedPoints s hs))).map gU ≫
      (Over.pullbackSquareObjIso
        (morphismRestrict_ι (S.fromSpecStalk (s i)) (complementOfClosedPoints s hs)) B).hom =
    (Over.pullbackSquareObjIso
        (morphismRestrict_ι (S.fromSpecStalk (s i)) (complementOfClosedPoints s hs)) A).hom ≫
      (Over.pullback (((S.fromSpecStalk (s i)) ⁻¹ᵁ
        (complementOfClosedPoints s hs)).ι)).map (gL i)

/-- **The overlap equation for the open member and a local member of the covering family.**  Any
scheme mapping compatibly to the base change of `A` to the open complement and to its base
change to the local scheme at `s i` sees the open component and the `i`-th local component of a
descent datum as the same morphism to `B`.

The compatible pair of maps is turned into a single map into the iterated base change over the
punctured local scheme — this uses that a morphism to the local scheme whose image in `S` lies
in the open complement factors through the puncture — and the equation is then the compatibility
square. -/
theorem descent_compatible_complement_local_raw (i : I)
    (hsq : PuncturedCompatible s hs gU gL i) {Z : Scheme.{u}}
    (g₁ : Z ⟶ pullback A.hom (complementOfClosedPoints s hs).ι)
    (g₂ : Z ⟶ pullback A.hom (S.fromSpecStalk (s i)))
    (h : g₁ ≫ pullback.fst A.hom (complementOfClosedPoints s hs).ι =
      g₂ ≫ pullback.fst A.hom (S.fromSpecStalk (s i))) :
    g₁ ≫ gU.left ≫ pullback.fst B.hom (complementOfClosedPoints s hs).ι =
      g₂ ≫ (gL i).left ≫ pullback.fst B.hom (S.fromSpecStalk (s i)) := by
  have hab : (g₂ ≫ pullback.snd A.hom (S.fromSpecStalk (s i))) ≫ S.fromSpecStalk (s i) =
      (g₁ ≫ pullback.snd A.hom (complementOfClosedPoints s hs).ι) ≫
        (complementOfClosedPoints s hs).ι :=
    (comp_pullback_snd_comp _ _ g₂).trans
      ((congrArg (· ≫ A.hom) h).symm.trans (comp_pullback_snd_comp _ _ g₁).symm)
  obtain ⟨b', hb'⟩ := LocalSchemesCover.exists_lift_puncturedLocalScheme s hs i
    (g₂ ≫ pullback.snd A.hom (S.fromSpecStalk (s i))) (by
      rw [hab]
      rintro _ ⟨w, rfl⟩
      exact (complementOfClosedPoints s hs).range_ι.le ⟨_, rfl⟩)
  have hw : ((S.fromSpecStalk (s i)) ∣_ (complementOfClosedPoints s hs)) ≫
      (complementOfClosedPoints s hs).ι =
      ((S.fromSpecStalk (s i)) ⁻¹ᵁ (complementOfClosedPoints s hs)).ι ≫
        S.fromSpecStalk (s i) :=
    morphismRestrict_ι (S.fromSpecStalk (s i)) (complementOfClosedPoints s hs)
  have h₁ : g₁ ≫ pullback.snd A.hom (complementOfClosedPoints s hs).ι =
      b' ≫ ((S.fromSpecStalk (s i)) ∣_ (complementOfClosedPoints s hs)) := by
    refine (cancel_mono (complementOfClosedPoints s hs).ι).1 (hab.symm.trans ?_)
    rw [Category.assoc b', hw, ← Category.assoc, hb']
  have hkey : pullback.fst (pullback.snd A.hom (complementOfClosedPoints s hs).ι)
        ((S.fromSpecStalk (s i)) ∣_ (complementOfClosedPoints s hs)) ≫
        gU.left ≫ pullback.fst B.hom (complementOfClosedPoints s hs).ι =
      (Over.pullbackSquareObjIso hw A).hom.left ≫
        pullback.fst (pullback.snd A.hom (S.fromSpecStalk (s i)))
            (((S.fromSpecStalk (s i)) ⁻¹ᵁ (complementOfClosedPoints s hs)).ι) ≫
          (gL i).left ≫ pullback.fst B.hom (S.fromSpecStalk (s i)) :=
    Over.pullbackSquare_fst_comp_left hw gU (gL i) hsq
  have hcross : pullback.lift g₁ b' h₁ ≫ (Over.pullbackSquareObjIso hw A).hom.left ≫
      pullback.fst (pullback.snd A.hom (S.fromSpecStalk (s i)))
        (((S.fromSpecStalk (s i)) ⁻¹ᵁ (complementOfClosedPoints s hs)).ι) = g₂ :=
    Over.pullbackSquareObjIso_lift_fst hw g₁ g₂ b' h₁ hb'.symm h
  rw [← pullback.lift_fst g₁ b' h₁, Category.assoc, hkey, reassoc_of% hcross]

/-- The family of elements of the descent problem solved by amalgamation: on the base change of
`A` to the open complement it is the open component of the given descent datum, and on the base
change to the local scheme at `s i` it is the `i`-th local component. -/
noncomputable def restrictionDescentFamilyRaw (a : Option I) :
    pullback A.hom (LocalSchemesCover.map s hs a) ⟶ B.left :=
  Option.rec (gU.left ≫ pullback.fst B.hom (complementOfClosedPoints s hs).ι)
    (fun i ↦ (gL i).left ≫ pullback.fst B.hom (S.fromSpecStalk (s i))) a

include hs in
/-- **The family is compatible**, so the descent problem has a solution.  An overlap of a member
with itself carries no condition because each member is a *monomorphism*; the overlap of the open
member with a local member is
`AlgebraicGeometry.descent_compatible_complement_local_raw`; and the overlap of two distinct local
members factors through the open member, so both of its sides are computed by that lemma. -/
theorem restrictionDescentFamilyRaw_compatible (hinj : Function.Injective s)
    (hsq : ∀ i, PuncturedCompatible s hs gU gL i) :
    Presieve.Arrows.Compatible (yoneda.obj B.left)
      (fun a ↦ pullback.fst A.hom (LocalSchemesCover.map s hs a))
      (restrictionDescentFamilyRaw s hs gU gL) := by
  intro a b Z ga gb hab
  match a, b with
  | none, none =>
    exact congrArg (· ≫ restrictionDescentFamilyRaw s hs gU gL none) ((cancel_mono _).1 hab)
  | none, some i => exact descent_compatible_complement_local_raw s hs gU gL i (hsq i) ga gb hab
  | some i, none =>
    exact (descent_compatible_complement_local_raw s hs gU gL i (hsq i) gb ga hab.symm).symm
  | some i, some j =>
    by_cases hij : i = j
    · subst hij
      exact congrArg (· ≫ restrictionDescentFamilyRaw s hs gU gL (some i)) ((cancel_mono _).1 hab)
    · obtain ⟨c, hc⟩ := LocalSchemesCover.exists_lift_complement_of_ne s hs hinj hij
        (z := (ga ≫ pullback.fst A.hom (S.fromSpecStalk (s i))) ≫ A.hom)
        (bi := ga ≫ pullback.snd A.hom (S.fromSpecStalk (s i)))
        (bj := gb ≫ pullback.snd A.hom (S.fromSpecStalk (s j)))
        (comp_pullback_snd_comp _ _ ga)
        ((comp_pullback_snd_comp _ _ gb).trans (congrArg (· ≫ A.hom) hab).symm)
      exact (descent_compatible_complement_local_raw s hs gU gL i (hsq i)
            (pullback.lift _ c hc.symm) ga (pullback.lift_fst _ _ _)).symm.trans
        (descent_compatible_complement_local_raw s hs gU gL j (hsq j) (pullback.lift _ c hc.symm) gb
          ((pullback.lift_fst _ _ _).trans hab))

include hs in
/-- **Amalgamation of morphisms near finitely many closed points, for arbitrary objects of
`Over S`.**  A morphism between the base changes of `A` and `B` to the open complement, together
with a family of morphisms between their base changes to the local schemes at the points, which
are compatible over the punctured local schemes, is the family of base changes of a single
morphism `A ⟶ B` over `S`.

This is the existence half of fpqc descent of morphisms for the covering family of
`AlgebraicGeometry.LocalSchemesCover.presieve₀_mem_fpqcPrecoverage`; the uniqueness half is
`AlgebraicGeometry.LocalSchemesCover.over_hom_ext_of_baseChange`, so the amalgamated morphism is
in fact unique.  Neither half asks `A` or `B` to be of finite presentation over `S`: the sheaf
condition is applied to the base change of the covering family along `A.hom`, which is a
covering family for every morphism to `S`.  Fullness of the canonical restriction functor of
[Stacks, Tag 0E8Q], `AlgebraicGeometry.full_canonicalRestrictionFunctor`, is the case of a
descent datum arising from a morphism of gluing data between finitely presented objects. -/
theorem exists_over_hom_of_baseChange (hinj : Function.Injective s)
    (hqc : QuasiCompact (complementOfClosedPoints s hs).ι)
    (hsq : ∀ i, PuncturedCompatible s hs gU gL i) :
    ∃ f : A ⟶ B, (Over.pullback (complementOfClosedPoints s hs).ι).map f = gU ∧
      ∀ i, (Over.pullback (S.fromSpecStalk (s i))).map f = gL i := by
  have hsndU : gU.left ≫ pullback.snd B.hom (complementOfClosedPoints s hs).ι =
      pullback.snd A.hom (complementOfClosedPoints s hs).ι := Over.w gU
  have hsndL : ∀ i, (gL i).left ≫ pullback.snd B.hom (S.fromSpecStalk (s i)) =
      pullback.snd A.hom (S.fromSpecStalk (s i)) := fun i ↦ Over.w (gL i)
  have hsf : Presieve.IsSheafFor (yoneda.obj B.left)
      (Presieve.ofArrows (fun a ↦ pullback A.hom (LocalSchemesCover.map s hs a))
        (fun a ↦ pullback.fst A.hom (LocalSchemesCover.map s hs a))) :=
    (GrothendieckTopology.Subcanonical.isSheaf_of_isRepresentable _).isSheafFor _
      (Precoverage.generate_mem_toGrothendieck
        (LocalSchemesCover.presieve_pullback_mem_fpqcPrecoverage s hs hqc A.hom))
  obtain ⟨t, ht, -⟩ := (Presieve.isSheafFor_arrows_iff _ _).1 hsf
    (restrictionDescentFamilyRaw s hs gU gL)
    (restrictionDescentFamilyRaw_compatible s hs gU gL hinj hsq)
  have htU : pullback.fst A.hom (complementOfClosedPoints s hs).ι ≫ t =
      gU.left ≫ pullback.fst B.hom (complementOfClosedPoints s hs).ι := ht none
  have htL : ∀ i : I, pullback.fst A.hom (S.fromSpecStalk (s i)) ≫ t =
      (gL i).left ≫ pullback.fst B.hom (S.fromSpecStalk (s i)) := fun i ↦ ht (some i)
  have hover : t ≫ B.hom = A.hom :=
    LocalSchemesCover.hom_ext_of_baseChange s hs hqc A.hom _ _ fun a ↦ by
      match a with
      | none =>
        exact ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ B.hom) htU)).trans
          (fst_comp_hom_of_comp_snd _ hsndU)
      | some i =>
        exact ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ B.hom) (htL i))).trans
          (fst_comp_hom_of_comp_snd _ (hsndL i))
  refine ⟨Over.homMk t hover, Over.OverMorphism.ext (pullback.hom_ext ?_ ?_),
    fun i ↦ Over.OverMorphism.ext (pullback.hom_ext ?_ ?_)⟩
  · exact (Over.pullback_map_left_comp_fst _ (Over.homMk t hover)).trans htU
  · exact (Over.w _).trans hsndU.symm
  · exact (Over.pullback_map_left_comp_fst _ (Over.homMk t hover)).trans (htL i)
  · exact (Over.w _).trans (hsndL i).symm

end Descent

section Full

variable {S : Scheme.{u}} {I : Type u} [Finite I] (s : I → S)
  (hs : ∀ i, s i ∈ closedPoints S) {X Y : FinitePresentationOver S}
  (g : (canonicalRestrictionFunctor s hs).obj X ⟶ (canonicalRestrictionFunctor s hs).obj Y)

/-- The open component of a morphism of gluing data, as a morphism between the base changes of
`X` and of `Y` to the open complement. -/
noncomputable def openComponentLeft :
    pullback X.obj.hom (complementOfClosedPoints s hs).ι ⟶
      pullback Y.obj.hom (complementOfClosedPoints s hs).ι :=
  g.hom.left.hom.left

/-- The `i`-th local component of a morphism of gluing data, as a morphism between the base
changes of `X` and of `Y` to the local scheme at `s i`. -/
noncomputable def localComponentLeft (i : I) :
    pullback X.obj.hom (S.fromSpecStalk (s i)) ⟶ pullback Y.obj.hom (S.fromSpecStalk (s i)) :=
  (g.hom.right i).hom.left

/-- The open component of a morphism of gluing data is a morphism over the open complement. -/
theorem openComponentLeft_comp_snd :
    openComponentLeft s hs g ≫ pullback.snd Y.obj.hom (complementOfClosedPoints s hs).ι =
      pullback.snd X.obj.hom (complementOfClosedPoints s hs).ι :=
  Over.w g.hom.left.hom

/-- The `i`-th local component of a morphism of gluing data is a morphism over the local scheme
at `s i`. -/
theorem localComponentLeft_comp_snd (i : I) :
    localComponentLeft s hs g i ≫ pullback.snd Y.obj.hom (S.fromSpecStalk (s i)) =
      pullback.snd X.obj.hom (S.fromSpecStalk (s i)) :=
  Over.w (g.hom.right i).hom

/-- **The commutative square carried by a morphism of gluing data**, read in `Over U_i` as the
compatibility of the base changes of the open and the `i`-th local component to the punctured
local scheme at `s i`, through the base-change comparison isomorphism of the square
`U_i ⟶ U ⟶ S = U_i ⟶ S_i ⟶ S`. -/
theorem gluingData_square (i : I) :
    (Over.pullback ((S.fromSpecStalk (s i)) ∣_ (complementOfClosedPoints s hs))).map
          g.hom.left.hom ≫
        (Over.pullbackSquareObjIso
          (morphismRestrict_ι (S.fromSpecStalk (s i)) (complementOfClosedPoints s hs))
          Y.obj).hom =
      (Over.pullbackSquareObjIso
          (morphismRestrict_ι (S.fromSpecStalk (s i)) (complementOfClosedPoints s hs))
          X.obj).hom ≫
        (Over.pullback (((S.fromSpecStalk (s i)) ⁻¹ᵁ
          (complementOfClosedPoints s hs)).ι)).map (g.hom.right i).hom :=
  congrArg InducedCategory.Hom.hom (congrFun g.hom.w i)

/-- The restriction of the open component to the base change of `X` is a morphism over `S`. -/
theorem openComponentLeft_descent_comp_hom :
    (openComponentLeft s hs g ≫ pullback.fst Y.obj.hom (complementOfClosedPoints s hs).ι) ≫
        Y.obj.hom =
      pullback.fst X.obj.hom (complementOfClosedPoints s hs).ι ≫ X.obj.hom :=
  fst_comp_hom_of_comp_snd _ (openComponentLeft_comp_snd s hs g)

/-- The restriction of the `i`-th local component to the base change of `X` is a morphism over
`S`. -/
theorem localComponentLeft_descent_comp_hom (i : I) :
    (localComponentLeft s hs g i ≫ pullback.fst Y.obj.hom (S.fromSpecStalk (s i))) ≫
        Y.obj.hom =
      pullback.fst X.obj.hom (S.fromSpecStalk (s i)) ≫ X.obj.hom :=
  fst_comp_hom_of_comp_snd _ (localComponentLeft_comp_snd s hs g i)

/-- **The overlap equation for the open member and a local member of the covering family.**  Any
scheme mapping compatibly to the base change of `X` to the open complement and to its base
change to the local scheme at `s i` sees the open and the `i`-th local component of a morphism
of gluing data as the same morphism to `Y`.

This is `AlgebraicGeometry.descent_compatible_complement_local_raw` for the descent datum
extracted from a morphism of gluing data, whose compatibility over the punctured local scheme at
`s i` is the commutative square `AlgebraicGeometry.gluingData_square`. -/
theorem descent_compatible_complement_local (i : I) {Z : Scheme.{u}}
    (g₁ : Z ⟶ pullback X.obj.hom (complementOfClosedPoints s hs).ι)
    (g₂ : Z ⟶ pullback X.obj.hom (S.fromSpecStalk (s i)))
    (h : g₁ ≫ pullback.fst X.obj.hom (complementOfClosedPoints s hs).ι =
      g₂ ≫ pullback.fst X.obj.hom (S.fromSpecStalk (s i))) :
    g₁ ≫ openComponentLeft s hs g ≫
        pullback.fst Y.obj.hom (complementOfClosedPoints s hs).ι =
      g₂ ≫ localComponentLeft s hs g i ≫ pullback.fst Y.obj.hom (S.fromSpecStalk (s i)) :=
  descent_compatible_complement_local_raw s hs g.hom.left.hom (fun i ↦ (g.hom.right i).hom) i
    (gluingData_square s hs g i) g₁ g₂ h

/-- The family of elements of the descent problem solved by fullness: on the base change of `X`
to the open complement it is the open component of the given morphism of gluing data, and on the
base change to the local scheme at `s i` it is the `i`-th local component. -/
noncomputable def restrictionDescentFamily (a : Option I) :
    pullback X.obj.hom (LocalSchemesCover.map s hs a) ⟶ Y.obj.left :=
  Option.rec
    (openComponentLeft s hs g ≫ pullback.fst Y.obj.hom (complementOfClosedPoints s hs).ι)
    (fun i ↦ localComponentLeft s hs g i ≫ pullback.fst Y.obj.hom (S.fromSpecStalk (s i))) a

include hs in
/-- **The family is compatible**, so the descent problem has a solution.  An overlap of a member
with itself carries no condition because each member is a monomorphism; the overlap of the open
member with a local member is
`AlgebraicGeometry.descent_compatible_complement_local`; and the overlap of two distinct local
members factors through the open member, so both of its sides are computed by that lemma. -/
theorem restrictionDescentFamily_compatible (hinj : Function.Injective s) :
    Presieve.Arrows.Compatible (yoneda.obj Y.obj.left)
      (fun a ↦ pullback.fst X.obj.hom (LocalSchemesCover.map s hs a))
      (restrictionDescentFamily s hs g) :=
  restrictionDescentFamilyRaw_compatible s hs g.hom.left.hom (fun i ↦ (g.hom.right i).hom) hinj
    (gluingData_square s hs g)

include hs in
/-- **Stacks Project, Tag 0E8Q**, the fullness constituent of the equivalence.  The canonical
restriction functor from schemes of finite presentation over `S` to gluing data near a finite
family of distinct closed points is full: a morphism over the open complement together with a
family of morphisms over the local schemes agreeing over the punctured local schemes comes from
a morphism over `S`.

The source of Tag 0E8Q omits the proof of full faithfulness; this is its full half, and it is
the amalgamation direction of fpqc descent for the covering family of
`AlgebraicGeometry.LocalSchemesCover.presieve₀_mem_fpqcPrecoverage`, specialized from
`AlgebraicGeometry.exists_over_hom_of_baseChange` to the components of a morphism of gluing
data. -/
theorem full_canonicalRestrictionFunctor (hinj : Function.Injective s)
    (hqc : QuasiCompact (complementOfClosedPoints s hs).ι) :
    (canonicalRestrictionFunctor s hs).Full where
  map_surjective := by
    intro X Y g
    obtain ⟨f, hfU, hfL⟩ := exists_over_hom_of_baseChange s hs g.hom.left.hom
      (fun i ↦ (g.hom.right i).hom) hinj hqc (gluingData_square s hs g)
    exact ⟨⟨f⟩, (ObjectProperty.ι _).map_injective (CommaMorphism.ext
      ((ObjectProperty.ι _).map_injective hfU)
      (funext fun i ↦ (ObjectProperty.ι _).map_injective (hfL i)))⟩

include hs in
/-- **Stacks Project, Tag 0E8Q**, full faithfulness.  The canonical restriction functor from
schemes of finite presentation over `S` to gluing data near a finite family of distinct closed
points is fully faithful.  This is the statement whose proof the source omits; the equivalence
asserted by the tag additionally needs essential surjectivity, which is
[Stacks, Tag 0BPA](https://stacks.math.columbia.edu/tag/0BPA) and is not proved here. -/
noncomputable def fullyFaithfulCanonicalRestrictionFunctor (hinj : Function.Injective s)
    (hqc : QuasiCompact (complementOfClosedPoints s hs).ι) :
    (canonicalRestrictionFunctor s hs).FullyFaithful :=
  haveI := full_canonicalRestrictionFunctor s hs hinj hqc
  haveI := faithful_canonicalRestrictionFunctor s hs hqc
  .ofFullyFaithful _

end Full

/-! ### The binders of the `equivalence` label of Tag 0E8Q, checked

Tag 0E8Q's `equivalence` label asserts
`(canonicalRestrictionFunctor s hs).IsEquivalence` under the binders

    {S : Scheme.{u}} {I : Type u} [Finite I] (s : I → ↥S)
    (hs : ∀ i, s i ∈ closedPoints ↥S) (hinj : Function.Injective s)
    (hqc : QuasiCompact (complementOfClosedPoints s hs).ι)

and nothing else.  The example below is that binder list verbatim, in the same order, with
`IsEquivalence` replaced by the two constituents proved so far: so neither constituent carries
a hypothesis the statement lacks, and once essential surjectivity (Tag 0BPA) is proved under these
same binders the label's single assertion follows with no extra hypothesis.  The label is *not*
attached yet, because its statement is that one `IsEquivalence` assertion, which fullness and
faithfulness alone do not give. -/
example {S : Scheme.{u}} {I : Type u} [Finite I] (s : I → S)
    (hs : ∀ i, s i ∈ closedPoints S) (hinj : Function.Injective s)
    (hqc : QuasiCompact (complementOfClosedPoints s hs).ι) :
    (canonicalRestrictionFunctor s hs).Full ∧ (canonicalRestrictionFunctor s hs).Faithful :=
  ⟨full_canonicalRestrictionFunctor s hs hinj hqc, faithful_canonicalRestrictionFunctor s hs hqc⟩

end AlgebraicGeometry

end
