module

public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.PullbackCarrier
public import Mathlib.CategoryTheory.Limits.Types.Pullbacks
public import Mathlib.CategoryTheory.Sites.Over
public import StacksFrontier.AlgebraicGeometry.Blowup.IsomorphismOffCenter.Basic
public import StacksFrontier.AlgebraicGeometry.Blowup.ReesAlgebra.Proper
public import StacksFrontier.AlgebraicGeometry.Flatness.SubschemeFinitePresentation
public import StacksFrontier.AlgebraicGeometry.Size.Cutoff
public import StacksFrontier.AlgebraicGeometry.Size.OpenCover
public import StacksFrontier.AlgebraicGeometry.Topologies.Ph.BigSite
public import StacksFrontier.AlgebraicGeometry.Topologies.Ph.Coverings
public import StacksFrontier.AlgebraicGeometry.Topologies.StandardPhRefinement
public import StacksFrontier.CategoryTheory.Sites.Pretopology.CombinatorialEquivalence
public import StacksCore.Tactic.StacksAttribute

/-!
# Descent for blow up squares in the ph topology

A blow up square consists of a scheme `X`, a closed subscheme `Z ⊆ X` whose inclusion is of
finite presentation, the blowup `b : X' ⟶ X` of `X` in `Z`, and the exceptional divisor
`E = b⁻¹(Z)`. A sheaf of sets on a big ph site sends such a square, all four of whose corners
lie in the site, to a cartesian square of sets: a section of the sheaf on `X` is the same thing
as a pair of sections on `Z` and on `X'` agreeing on `E`.

## Main results

* `AlgebraicGeometry.BigPHOver.isPullback_map_of_blowUpSquare`: the square of sections of a ph
  sheaf on a blow up square is cartesian.

## Implementation notes

The disjoint union `Z ⨿ X' ⟶ X` is proper and surjective, hence a ph covering, and the assertion
is the sheaf condition for that covering. Rather than form the coproduct inside the site and
compute its self-fibre product, the proof works with the two-element family `{Z ⟶ X, X' ⟶ X}`
directly: the sieve it generates is covering because it is refined by the singleton covering on a
coproduct of the two objects, and compatibility of a pair of sections on the four overlaps
reduces to the three cases `Z ×_X Z = Z`, `Z ×_X X' = E = X' ×_X Z` and `X' ×_X X'`. Only the
last case has content, and there the two restrictions of the section on `X'` to an object `W`
mapping to `X'` in two ways agree because the pullback of `W` along the centre and the equalizer
of the two maps jointly cover `W`, the blowup being an isomorphism away from the centre.

The three corners other than the base are arbitrary objects of the site identified with the
canonical constructions: `Z` over `X` with the closed subscheme cut out by an ideal sheaf, `X'`
over `X` with the blowup in that ideal sheaf, and `E` as the fibre product of the other two.
This allows any presentation of a blow up square in the site.

## References

* [Stacks Project, Tag 0EW1](https://stacks.math.columbia.edu/tag/0EW1)
* [Stacks Project, Tag 0EV5](https://stacks.math.columbia.edu/tag/0EV5)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u v

namespace AlgebraicGeometry

namespace BigPHOver

/-- A coproduct of two objects of the cutoff category of a big ph site is again one: its size is
the size of the coproduct of a two-element family of schemes, which is below the cutoff because
the cutoff is uncountable with uncountable cofinality. -/
private theorem contains_coprod (B : BigPHSite.{u}) {X Y : Scheme.{u}}
    (hX : B.Contains X) (hY : B.Contains Y) : B.Contains (X ⨿ Y) := by
  change (X ⨿ Y).size < B.cutoff
  rw [Scheme.size_congr (coprodIsoSigma X Y)]
  apply Scheme.size_sigmaObj_lt B.aleph0_lt_cutoff B.aleph0_lt_cutoff_cof
  · simp
  · intro i
    cases i.down <;> assumption

/-- The object of a big ph site over `S` on the source of a closed immersion into the underlying
scheme of an object of the site. -/
private def ofClosedImmersion (B : BigPHSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {W : BigPHOver B S hS} {A : Scheme.{u}} (a : A ⟶ W.left.obj) [IsClosedImmersion a] :
    BigPHOver B S hS :=
  Over.mk (ObjectProperty.homMk (a ≫ W.hom.hom) :
    B.obj A (Scheme.size_lt_of_isClosedImmersion a W.left.property) ⟶ B.obj S hS)

/-- The structure morphism of `ofClosedImmersion` to the ambient object of the site. -/
private def homOfClosedImmersion (B : BigPHSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {W : BigPHOver B S hS} {A : Scheme.{u}} (a : A ⟶ W.left.obj) [IsClosedImmersion a] :
    ofClosedImmersion B S hS a ⟶ W :=
  Over.homMk (ObjectProperty.homMk a)

/-- The object of a big ph site over `S` on the coproduct of the sources of two morphisms with a
common target. -/
private def coprodOver (B : BigPHSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y T : BigPHOver B S hS} (f : X ⟶ T) (g : Y ⟶ T) : BigPHOver B S hS :=
  Over.mk (ObjectProperty.homMk (coprod.desc ((BigPHOver.toScheme B S hS).map f)
        ((BigPHOver.toScheme B S hS).map g) ≫ T.hom.hom) :
    B.obj (X.left.obj ⨿ Y.left.obj) (contains_coprod B X.left.property Y.left.property) ⟶
      B.obj S hS)

/-- The morphism to the common target out of `coprodOver`. -/
private def coprodOverDesc (B : BigPHSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y T : BigPHOver B S hS} (f : X ⟶ T) (g : Y ⟶ T) : coprodOver B S hS f g ⟶ T :=
  Over.homMk (ObjectProperty.homMk (coprod.desc ((BigPHOver.toScheme B S hS).map f)
    ((BigPHOver.toScheme B S hS).map g)))

/-- Being a ph covering transfers along an equality of the family of sources together with a
pointwise heterogeneous equality of the structure morphisms. -/
private theorem isPHCovering_congr {T : Scheme.{u}} {ι : Type v} {A A' : ι → Scheme.{u}}
    (hA : A = A') {a : ∀ i, A i ⟶ T} {a' : ∀ i, A' i ⟶ T} (ha : ∀ i, HEq (a i) (a' i))
    (h : IsPHCovering A a) : IsPHCovering A' a' := by
  subst hA
  obtain rfl : a = a' := funext fun i => eq_of_heq (ha i)
  exact h

/-- A family in a big ph site over `S` whose image in all schemes is a ph covering generates a
covering sieve for the localized topology. -/
private theorem ph_sieve_mem_topology
    (B : BigPHSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X : BigPHOver B S hS} (E : PreZeroHypercover.{u + 1} X)
    (hE : IsPHCovering (E.map (BigPHOver.toScheme B S hS)).X
      (E.map (BigPHOver.toScheme B S hS)).f) :
    Sieve.generate E.presieve₀ ∈ BigPHOver.topology B S hS X := by
  let D := E.map (BigPHOver.forget B S hS)
  obtain ⟨⟨target, family⟩, hfamily, htarget, hcomb⟩ :=
    B.covering_representative ⟨X.left, D⟩ hE
  change X.left = target at htarget
  subst target
  rw [BigPHOver.topology, GrothendieckTopology.mem_over_iff]
  change Sieve.overEquiv X (Sieve.ofArrows E.X E.f) ∈ B.topology X.left
  rw [Sieve.overEquiv_ofArrows]
  exact (Precoverage.generate_mem_toGrothendieck
    (PreZeroHypercover.presieve₀_eq_of_combinatoriallyEquivalent hcomb ▸
      (BigPHSite.mem_precoverage_iff B).2 ⟨family, rfl, hfamily⟩) :
    Sieve.generate D.presieve₀ ∈ B.topology X.left)

/-- The sieve generated by a single proper surjective morphism of a big ph site over `S` is a
covering sieve: a proper surjection of schemes is a ph covering, and the localized topology on
the slice over `S` is generated by the ph coverings of the underlying schemes. -/
private theorem singleton_sieve_mem_topology
    (B : BigPHSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : BigPHOver B S hS} (f : Y ⟶ X)
    [Surjective (B.inclusion.map f.left)] [IsProper (B.inclusion.map f.left)] :
    Sieve.generate (Presieve.singleton f) ∈ BigPHOver.topology B S hS X := by
  have hphSmall := surjective_proper_isPHCovering (B.inclusion.map f.left)
  rw [isPHCovering_iff] at hphSmall
  have hphBig : IsPHCovering (fun _ : PUnit.{u + 2} => B.inclusion.obj Y.left)
      (fun _ => B.inclusion.map f.left) := by
    rw [isPHCovering_iff]
    refine ⟨fun _ => hphSmall.1 (), fun U hU => ?_⟩
    obtain ⟨𝒰, hstd, ⟨φ⟩⟩ := hphSmall.2 U hU
    exact ⟨𝒰, hstd, ⟨φ.comp {
      s₀ := fun _ => ⟨⟩
      h₀ := fun _ => 𝟙 _
      w₀ := fun _ => by simp [PreZeroHypercover.pullback₂] }⟩⟩
  simpa using ph_sieve_mem_topology B S hS (PreZeroHypercover.singleton f) hphBig

/-- The morphism out of a coproduct determined by two proper morphisms to a common target is
proper: it factors as the coproduct of the two morphisms followed by the codiagonal, and
properness of a coproduct of morphisms is Zariski local on the target. -/
private theorem isProper_coprod_desc {X Y T : Scheme.{u}} (f : X ⟶ T) (g : Y ⟶ T)
    [IsProper f] [IsProper g] : IsProper (coprod.desc f g) := by
  have : IsProper (coprod.map f g) :=
    IsZariskiLocalAtTarget.coprodMap (P := @IsProper) f g inferInstance inferInstance
  rw [show coprod.desc f g = coprod.map f g ≫ coprod.desc (𝟙 T) (𝟙 T) by
    apply coprod.hom_ext <;> simp]
  infer_instance

/-- The morphism out of a coproduct determined by two morphisms whose ranges jointly cover the
common target is surjective. -/
private theorem surjective_coprod_desc {X Y T : Scheme.{u}} (f : X ⟶ T) (g : Y ⟶ T)
    (hcover : Set.range f ∪ Set.range g = Set.univ) : Surjective (coprod.desc f g) := by
  constructor
  intro point
  rcases hcover.ge (Set.mem_univ point) with ⟨preimage, rfl⟩ | ⟨preimage, rfl⟩
  · exact ⟨(coprod.inl : X ⟶ X ⨿ Y) preimage, by rw [← Scheme.Hom.comp_apply, coprod.inl_desc]⟩
  · exact ⟨(coprod.inr : Y ⟶ X ⨿ Y) preimage, by rw [← Scheme.Hom.comp_apply, coprod.inr_desc]⟩

/-- A sieve is covering as soon as it becomes covering after pullback along a morphism whose
singleton presieve generates a covering sieve. -/
private theorem mem_of_pullback_mem_singleton {C : Type*} [Category C]
    (J : GrothendieckTopology C) {D T : C} (dd : D ⟶ T)
    (hdd : Sieve.generate (Presieve.singleton dd) ∈ J T) (R : Sieve T)
    (hR : R.pullback dd ∈ J D) : R ∈ J T := by
  apply J.transitive hdd R
  rintro source arrow ⟨middle, second, first, hfirst, rfl⟩
  cases hfirst
  simpa only [Sieve.pullback_comp] using J.pullback_stable second hR

/-- A sieve on the common target of two morphisms that contains them both becomes covering after
pullback along the morphism out of the coproduct of their sources, because the two coprojections
of the coproduct open cover refine it. -/
private theorem pullback_mem_topology_of_mem_of_mem
    (B : BigPHSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y T : BigPHOver B S hS} (f : X ⟶ T) (g : Y ⟶ T) (R : Sieve T) (hf : R f) (hg : R g) :
    R.pullback (coprodOverDesc B S hS f g) ∈
      BigPHOver.topology B S hS (coprodOver B S hS f g) := by
  let d := coprod.desc ((BigPHOver.toScheme B S hS).map f) ((BigPHOver.toScheme B S hS).map g)
  let D := coprodOver B S hS f g
  let dd := coprodOverDesc B S hS f g
  let C := coprodOpenCover.{u, u + 1} X.left.obj Y.left.obj
  let family : PreZeroHypercover.{u + 1} D := {
    I₀ := C.I₀
    X := fun side => side.elim (fun _ => X) (fun _ => Y)
    f := fun side => Sum.rec (motive := fun choice =>
      choice.elim (fun _ => X) (fun _ => Y) ⟶ D)
      (fun _ => Over.homMk (ObjectProperty.homMk coprod.inl) (by
        ext
        change coprod.inl ≫ (d ≫ T.hom.hom) = X.hom.hom
        rw [← Category.assoc, coprod.inl_desc]
        exact congrArg (fun arrow => arrow.hom) f.w))
      (fun _ => Over.homMk (ObjectProperty.homMk coprod.inr) (by
        ext
        change coprod.inr ≫ (d ≫ T.hom.hom) = Y.hom.hom
        rw [← Category.assoc, coprod.inr_desc]
        exact congrArg (fun arrow => arrow.hom) g.w)) side }
  refine (BigPHOver.topology B S hS).superset_covering ((Sieve.generate_le_iff _ _).mpr ?_)
    (ph_sieve_mem_topology B S hS family (isPHCovering_congr
      (by funext side; cases side <;> rfl) (fun side => by cases side <;> rfl)
      (IsPHCovering.of_openCover C)))
  rintro source arrow ⟨side⟩
  cases side with
  | inl index =>
    change R (family.f (Sum.inl index) ≫ dd)
    rw [show family.f (Sum.inl index) ≫ dd = f by
      ext
      simp only [family, dd, coprodOverDesc, Over.comp_left,
        ObjectProperty.FullSubcategory.comp_hom, Over.homMk_left]
      exact coprod.inl_desc _ _]
    exact hf
  | inr index =>
    change R (family.f (Sum.inr index) ≫ dd)
    rw [show family.f (Sum.inr index) ≫ dd = g by
      ext
      simp only [family, dd, coprodOverDesc, Over.comp_left,
        ObjectProperty.FullSubcategory.comp_hom, Over.homMk_left]
      exact coprod.inr_desc _ _]
    exact hg

/-- Two proper morphisms of a big ph site over `S` whose underlying morphisms of schemes have
jointly surjective ranges generate a covering sieve: the induced morphism from the coproduct of
their sources is proper and surjective, hence covering, and it is refined by the two morphisms
because the two coprojections cover the coproduct. -/
private theorem two_arrows_sieve_mem_topology
    (B : BigPHSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y T : BigPHOver B S hS} (f : X ⟶ T) (g : Y ⟶ T)
    [IsProper ((BigPHOver.toScheme B S hS).map f)]
    [IsProper ((BigPHOver.toScheme B S hS).map g)]
    (hcover : Set.range ((BigPHOver.toScheme B S hS).map f) ∪
      Set.range ((BigPHOver.toScheme B S hS).map g) = Set.univ) :
    Sieve.generate (Presieve.ofArrows
      (fun side : ULift.{u + 1} Bool => Bool.casesOn side.down X Y)
      (fun side => Bool.casesOn (motive := fun choice =>
        Bool.casesOn choice X Y ⟶ T) side.down f g)) ∈ BigPHOver.topology B S hS T := by
  let f₀ := (BigPHOver.toScheme B S hS).map f
  let g₀ := (BigPHOver.toScheme B S hS).map g
  let dd := coprodOverDesc B S hS f g
  have : IsProper (coprod.desc f₀ g₀) := isProper_coprod_desc f₀ g₀
  have : Surjective (coprod.desc f₀ g₀) := surjective_coprod_desc f₀ g₀ hcover
  have : Surjective (B.inclusion.map dd.left) := inferInstanceAs (Surjective (coprod.desc f₀ g₀))
  have : IsProper (B.inclusion.map dd.left) := inferInstanceAs (IsProper (coprod.desc f₀ g₀))
  exact mem_of_pullback_mem_singleton (BigPHOver.topology B S hS) dd
    (singleton_sieve_mem_topology B S hS dd) _
    (pullback_mem_topology_of_mem_of_mem B S hS f g _
      (Sieve.le_generate _ _ _ (Presieve.ofArrows.mk (ULift.up false)))
      (Sieve.le_generate _ _ _ (Presieve.ofArrows.mk (ULift.up true))))

/-- Two sections of a ph sheaf over an object of the site are equal as soon as they agree along
two proper morphisms into that object whose ranges cover it. -/
private theorem eq_of_two_proper_arrows
    (B : BigPHSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : (BigPHOver B S hS)ᵒᵖ ⥤ Type v)
    (hF : Presheaf.IsSheaf (BigPHOver.topology B S hS) F)
    {X Y T : BigPHOver B S hS} (f : X ⟶ T) (g : Y ⟶ T)
    [IsProper ((BigPHOver.toScheme B S hS).map f)]
    [IsProper ((BigPHOver.toScheme B S hS).map g)]
    (hcover : Set.range ((BigPHOver.toScheme B S hS).map f) ∪
      Set.range ((BigPHOver.toScheme B S hS).map g) = Set.univ)
    {first second : F.obj (.op T)}
    (hf : F.map f.op first = F.map f.op second)
    (hg : F.map g.op first = F.map g.op second) : first = second := by
  apply ((Presieve.isSheafFor_iff_generate _).2
    (hF.isSheafFor _ (two_arrows_sieve_mem_topology B S hS f g hcover))).isSeparatedFor.ext
  rintro source arrow ⟨⟨side⟩⟩
  cases side <;> assumption

/-- An object `W` mapping to the blowup in two ways over the base is covered by its pullback
along the centre together with the equalizer of the two maps: a point of `W` lying outside the
centre lands in the open locus where the blowup is an isomorphism, and there the two maps agree
because they agree after composing with the blowup. -/
private theorem range_pullback_union_range_equalizer
    {W Y X Z : Scheme.{u}} (b : Y ⟶ X) (z : Z ⟶ X)
    [IsSeparated b] (U : X.Opens) [IsIso (b ∣_ U)]
    (hU : (U : Set X) = (Set.range z)ᶜ)
    (first second : W ⟶ Y) (hw : first ≫ b = second ≫ b) :
    Set.range (pullback.fst (first ≫ b) z) ∪
      Set.range (equalizer.ι (Over.homMk first : Over.mk (first ≫ b) ⟶ Over.mk b)
        (Over.homMk second hw.symm)).left = Set.univ := by
  refine Set.eq_univ_of_forall fun point => ?_
  by_cases hpoint : (first ≫ b) point ∈ Set.range z
  · left
    rwa [Scheme.Pullback.range_fst]
  · right
    let V : W.Opens := (first ≫ b) ⁻¹ᵁ U
    have hV : point ∈ V := by
      change (first ≫ b) point ∈ (U : Set X)
      rwa [hU]
    have hfirst : V ≤ first ⁻¹ᵁ (b ⁻¹ᵁ U) := by
      rw [← Scheme.Hom.comp_preimage]
    have hsecond : V ≤ second ⁻¹ᵁ (b ⁻¹ᵁ U) := by
      rw [← Scheme.Hom.comp_preimage, ← hw]
    have heq : V.ι ≫ first = V.ι ≫ second := by
      have hrestr : first.resLE (b ⁻¹ᵁ U) V hfirst = second.resLE (b ⁻¹ᵁ U) V hsecond := by
        apply (cancel_mono (b ∣_ U)).mp
        apply (cancel_mono U.ι).mp
        simp only [Category.assoc, morphismRestrict_ι, Scheme.Hom.resLE_comp_ι_assoc]
        rw [hw]
      simpa only [Scheme.Hom.resLE_comp_ι] using
        congrArg (fun arrow => arrow ≫ (b ⁻¹ᵁ U).ι) hrestr
    let p : Over.mk (first ≫ b) ⟶ Over.mk b := Over.homMk first
    let q : Over.mk (first ≫ b) ⟶ Over.mk b := Over.homMk second hw.symm
    let inclusion : Over.mk (V.ι ≫ (first ≫ b)) ⟶ Over.mk (first ≫ b) := Over.homMk V.ι
    have hpq : inclusion ≫ p = inclusion ≫ q := by
      ext
      exact heq
    let lift := equalizer.lift inclusion hpq
    have hlift : lift.left ≫ (equalizer.ι p q).left = V.ι :=
      congrArg Over.Hom.left (equalizer.lift_ι inclusion hpq)
    have hpt : point ∈ Set.range (⇑V.ι) := ⟨⟨point, hV⟩, rfl⟩
    rw [← hlift] at hpt
    obtain ⟨w, hw'⟩ := hpt
    rw [Scheme.Hom.comp_apply] at hw'
    exact ⟨lift.left w, hw'⟩

/-- A morphism that is an isomorphism over the open complement of the range of a second morphism
has range covering the common target together with it. -/
private theorem range_union_range_eq_univ {X Y Z : Scheme.{u}} (b : Y ⟶ X) (z : Z ⟶ X)
    (U : X.Opens) [IsIso (b ∣_ U)] (hU : (U : Set X) = (Set.range z)ᶜ) :
    Set.range z ∪ Set.range b = Set.univ := by
  refine Set.eq_univ_of_forall fun point => ?_
  by_cases hp : point ∈ Set.range z
  · exact Or.inl hp
  · right
    have hpU : point ∈ U := by
      change point ∈ (U : Set X)
      rwa [hU]
    obtain ⟨preimage, hpreimage⟩ := (b ∣_ U).surjective ⟨point, hpU⟩
    exact ⟨preimage.val, (morphismRestrict_base_coe b U preimage).symm.trans
      (congrArg Subtype.val hpreimage)⟩

/-- A morphism isomorphic over the base to the blowup of a finitely presented centre is proper,
the centre is a closed immersion, and the blowup is an isomorphism over the open complement of
the centre. -/
private theorem isProper_isClosedImmersion_exists_isIso_of_blowUpSquare {X Y Z : Scheme.{u}}
    (b : Y ⟶ X) (z : Z ⟶ X) (I : X.IdealSheafData) (hI : FinitePresentation I.subschemeι)
    (hb : Nonempty (Over.mk b ≅ Over.mk (blowUpToBase I)))
    (hZ : Nonempty (Over.mk z ≅ Over.mk I.subschemeι)) :
    IsProper b ∧ IsClosedImmersion z ∧
      ∃ U : X.Opens, (U : Set X) = (Set.range z)ᶜ ∧ IsIso (b ∣_ U) := by
  let isoBlowUp := Classical.choice hb
  let isoCenter := Classical.choice hZ
  have hisoBlowUp : IsIso isoBlowUp.hom.left := ((Over.forget _).mapIso isoBlowUp).isIso_hom
  have hisoCenter : IsIso isoCenter.hom.left := ((Over.forget _).mapIso isoCenter).isIso_hom
  have hwBlowUp : isoBlowUp.hom.left ≫ blowUpToBase I = b := by
    simpa only [Over.mk_hom] using isoBlowUp.hom.w
  have hwCenter : isoCenter.hom.left ≫ I.subschemeι = z := by
    simpa only [Over.mk_hom] using isoCenter.hom.w
  have hproperBlowUp : IsProper (blowUpToBase I) :=
    isProper_blowUpToBase_of_fg I ((Stacks.Flatness.finitePresentation_subschemeι_iff I).mp hI)
  have hclosed : IsClosedImmersion z :=
    hwCenter ▸ (inferInstance : IsClosedImmersion (isoCenter.hom.left ≫ I.subschemeι))
  have hcenterRange : Set.range z = I.support := by
    rw [← hwCenter]
    change Set.range (I.subschemeι ∘ isoCenter.hom.left) = (I.support : Set X)
    rw [Set.range_comp, range_eq_univ, Set.image_univ, I.range_subschemeι]
  let U : X.Opens := ⟨(I.support : Set X)ᶜ, I.support.isClosed.isOpen_compl⟩
  have hU : (U : Set X) = (Set.range z)ᶜ := by
    rw [hcenterRange]
    rfl
  have hisoBase : IsIso (blowUpToBase I ∣_ U) := isIso_blowUp_restrict_compl_support I
  have hisoRestrict : IsIso (isoBlowUp.hom.left ∣_ (blowUpToBase I ⁻¹ᵁ U)) := inferInstance
  refine ⟨hwBlowUp ▸ (inferInstance : IsProper (isoBlowUp.hom.left ≫ blowUpToBase I)), hclosed,
    U, hU, ?_⟩
  rw [← hwBlowUp, morphismRestrict_comp]
  exact IsIso.comp_isIso' hisoRestrict hisoBase

/-- Functoriality of a presheaf of types, in the form used for successive restrictions. -/
private theorem map_op_map_op {C : Type*} [Category C] {F : Cᵒᵖ ⥤ Type v}
    {A A' A'' : C} (u : A ⟶ A') (v : A' ⟶ A'') (x : F.obj (.op A'')) :
    F.map u.op (F.map v.op x) = F.map (u ≫ v).op x := by
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp]

/-- A pair of sections on the centre and on the blowup agreeing on the exceptional divisor has
equal restrictions along any pair of morphisms into the centre and into the blowup that agree over
the base, because such a pair factors through the exceptional divisor. -/
private theorem map_eq_map_of_comp_eq
    (B : BigPHSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : (BigPHOver B S hS)ᵒᵖ ⥤ Type v)
    {X Y Z E : BigPHOver B S hS} {b : Y ⟶ X} {z : Z ⟶ X} {p : E ⟶ Y} {e : E ⟶ Z}
    (hSquare : IsPullback e p z b)
    {centerSection : F.obj (.op Z)} {blowUpSection : F.obj (.op Y)}
    (hsections : F.map e.op centerSection = F.map p.op blowUpSection)
    {W : BigPHOver B S hS} (u : W ⟶ Z) (v : W ⟶ Y) (huv : u ≫ z = v ≫ b) :
    F.map u.op centerSection = F.map v.op blowUpSection := by
  let lift := hSquare.lift u v huv
  calc F.map u.op centerSection = F.map lift.op (F.map e.op centerSection) := by
        rw [map_op_map_op, hSquare.lift_fst u v huv]
    _ = F.map lift.op (F.map p.op blowUpSection) := congrArg _ hsections
    _ = F.map v.op blowUpSection := by rw [map_op_map_op, hSquare.lift_snd u v huv]

/-- Two restrictions of the section on the blowup along morphisms that agree over the base become
equal after further restriction along a morphism factoring through the centre. -/
private theorem map_eq_map_of_comp_center
    (B : BigPHSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : (BigPHOver B S hS)ᵒᵖ ⥤ Type v)
    {X Y Z E : BigPHOver B S hS} {b : Y ⟶ X} {z : Z ⟶ X} {p : E ⟶ Y} {e : E ⟶ Z}
    (hSquare : IsPullback e p z b)
    {centerSection : F.obj (.op Z)} {blowUpSection : F.obj (.op Y)}
    (hsections : F.map e.op centerSection = F.map p.op blowUpSection)
    {W V : BigPHOver B S hS} {first second : W ⟶ Y} (hw : first ≫ b = second ≫ b)
    (c : V ⟶ W) (k : V ⟶ Z) (hck : c ≫ first ≫ b = k ≫ z) :
    F.map c.op (F.map first.op blowUpSection) =
      F.map c.op (F.map second.op blowUpSection) := by
  have hcfirst : k ≫ z = (c ≫ first) ≫ b := by rw [Category.assoc, hck]
  have hcsecond : k ≫ z = (c ≫ second) ≫ b := by rw [Category.assoc, ← hw, hck]
  rw [map_op_map_op, map_op_map_op,
    ← map_eq_map_of_comp_eq B S hS F hSquare hsections k _ hcfirst,
    ← map_eq_map_of_comp_eq B S hS F hSquare hsections k _ hcsecond]

/-- The section of a ph sheaf on the blowup has equal restrictions along any two morphisms into
the blowup that agree over the base: the two restrictions agree on the pullback along the centre,
because there both are computed from the section on the centre, and on the equalizer of the two
morphisms, and those two closed subschemes cover the source. -/
private theorem map_eq_of_comp_blowUp_eq
    (B : BigPHSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : (BigPHOver B S hS)ᵒᵖ ⥤ Type v)
    (hF : Presheaf.IsSheaf (BigPHOver.topology B S hS) F)
    {X Y Z E : BigPHOver B S hS} (b : Y ⟶ X) (z : Z ⟶ X) (p : E ⟶ Y) (e : E ⟶ Z)
    [IsProper ((BigPHOver.toScheme B S hS).map b)]
    [IsClosedImmersion ((BigPHOver.toScheme B S hS).map z)]
    (hSquare : IsPullback e p z b)
    (U : X.left.obj.Opens)
    [IsIso ((BigPHOver.toScheme B S hS).map b ∣_ U)]
    (hU : (U : Set X.left.obj) = (Set.range ((BigPHOver.toScheme B S hS).map z))ᶜ)
    (centerSection : F.obj (.op Z)) (blowUpSection : F.obj (.op Y))
    (hsections : F.map e.op centerSection = F.map p.op blowUpSection)
    {W : BigPHOver B S hS} (first second : W ⟶ Y) (hw : first ≫ b = second ≫ b) :
    F.map first.op blowUpSection = F.map second.op blowUpSection := by
  let toScheme := BigPHOver.toScheme B S hS
  let b₀ := toScheme.map b
  let z₀ := toScheme.map z
  let first₀ := toScheme.map first
  let second₀ := toScheme.map second
  have : IsProper b₀ := inferInstance
  have : IsSeparated (Over.mk b₀).hom := inferInstanceAs (IsSeparated b₀)
  have hw₀ : first₀ ≫ b₀ = second₀ ≫ b₀ := by
    simpa only [Functor.map_comp] using congrArg toScheme.map hw
  let C₀ := pullback (first₀ ≫ b₀) z₀
  let c₀ : C₀ ⟶ W.left.obj := pullback.fst (first₀ ≫ b₀) z₀
  let k₀ : C₀ ⟶ Z.left.obj := pullback.snd (first₀ ≫ b₀) z₀
  have : IsClosedImmersion c₀ := inferInstance
  let c : ofClosedImmersion B S hS c₀ ⟶ W := homOfClosedImmersion B S hS c₀
  let k : ofClosedImmersion B S hS c₀ ⟶ Z := Over.homMk (ObjectProperty.homMk k₀) (by
    ext
    have hZ := congrArg (fun arrow => arrow.hom) z.w
    have hW := congrArg (fun arrow => arrow.hom) (first ≫ b).w
    change k₀ ≫ Z.hom.hom = c₀ ≫ W.hom.hom
    rw [← hZ, ← hW]
    simp only [ObjectProperty.FullSubcategory.comp_hom, Over.comp_left]
    change k₀ ≫ z₀ ≫ X.hom.hom = c₀ ≫ (first₀ ≫ b₀) ≫ X.hom.hom
    rw [← Category.assoc, ← Category.assoc, pullback.condition])
  have hcenter := map_eq_map_of_comp_center B S hS F hSquare hsections hw c k (by
    ext
    exact pullback.condition)
  let firstOver : Over.mk (first₀ ≫ b₀) ⟶ Over.mk b₀ := Over.homMk first₀
  let secondOver : Over.mk (first₀ ≫ b₀) ⟶ Over.mk b₀ := Over.homMk second₀ hw₀.symm
  let D₀ := (equalizer firstOver secondOver).left
  let d₀ : D₀ ⟶ W.left.obj := (equalizer.ι firstOver secondOver).left
  have : IsClosedImmersion d₀ := inferInstance
  let d : ofClosedImmersion B S hS d₀ ⟶ W := homOfClosedImmersion B S hS d₀
  have hd : d ≫ first = d ≫ second := by
    ext
    exact congrArg Over.Hom.left (equalizer.condition firstOver secondOver)
  have hequalizer : F.map d.op (F.map first.op blowUpSection) =
      F.map d.op (F.map second.op blowUpSection) := by
    rw [map_op_map_op, map_op_map_op, hd]
  have : IsProper (toScheme.map c) := inferInstanceAs (IsProper c₀)
  have : IsProper (toScheme.map d) := inferInstanceAs (IsProper d₀)
  exact eq_of_two_proper_arrows B S hS F hF c d
    (range_pullback_union_range_equalizer b₀ z₀ U hU first₀ second₀ hw₀)
    hcenter hequalizer

/-- **Stacks Project, Tag 0EW1.** Let `F` be a sheaf of sets on a big ph site over `S`. For every
blow up square in that site — a closed centre `Z ⊆ X` of finite presentation, the blowup
`b : X' ⟶ X` of `X` in `Z`, and the exceptional divisor `E = b⁻¹(Z)` — the square of restriction
maps `F(X) → F(Z) → F(E)` and `F(X) → F(X') → F(E)` is cartesian in the category of sets. -/
@[stacks 0EW1]
public theorem isPullback_map_of_blowUpSquare
    (B : BigPHSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : (BigPHOver B S hS)ᵒᵖ ⥤ Type v)
    (hF : Presheaf.IsSheaf (BigPHOver.topology B S hS) F)
    {X X' Z E : BigPHOver B S hS}
    (b : X' ⟶ X) (z : Z ⟶ X) (p : E ⟶ X') (e : E ⟶ Z)
    (I : ((BigPHOver.toScheme B S hS).obj X).IdealSheafData)
    (hI : FinitePresentation I.subschemeι)
    (hb : Nonempty (Over.mk ((BigPHOver.toScheme B S hS).map b) ≅ Over.mk (blowUpToBase I)))
    (hZ : Nonempty (Over.mk ((BigPHOver.toScheme B S hS).map z) ≅ Over.mk I.subschemeι))
    (hSquare : IsPullback
      ((BigPHOver.toScheme B S hS).map e) ((BigPHOver.toScheme B S hS).map p)
      ((BigPHOver.toScheme B S hS).map z) ((BigPHOver.toScheme B S hS).map b)) :
    IsPullback (F.map z.op) (F.map b.op) (F.map e.op) (F.map p.op) := by
  let toScheme := BigPHOver.toScheme B S hS
  let b₀ := toScheme.map b
  let z₀ := toScheme.map z
  obtain ⟨hproper, hclosed, U, hU, hisoB⟩ :=
    isProper_isClosedImmersion_exists_isIso_of_blowUpSquare b₀ z₀ I hI hb hZ
  have hSquareSite : IsPullback e p z b := hSquare.of_map_of_faithful toScheme
  have : Mono z := toScheme.mono_of_mono_map (inferInstanceAs (Mono z₀))
  have hcover : Set.range z₀ ∪ Set.range b₀ = Set.univ :=
    range_union_range_eq_univ b₀ z₀ U hU
  have : IsProper (toScheme.map z) := inferInstanceAs (IsProper z₀)
  have : IsProper (toScheme.map b) := inferInstanceAs (IsProper b₀)
  refine (Types.isPullback_iff _ _ _ _).mpr ⟨?_, ?_, ?_⟩
  · simp only [← Functor.map_comp, ← op_comp, hSquareSite.w]
  · intro first second hsections
    exact eq_of_two_proper_arrows B S hS F hF z b hcover hsections.1 hsections.2
  · intro centerSection blowUpSection hsections
    let family : PreZeroHypercover.{u + 1} X := {
      I₀ := ULift.{u + 1} Bool
      X := fun side => Bool.casesOn side.down Z X'
      f := fun side => Bool.casesOn (motive := fun choice =>
        Bool.casesOn choice Z X' ⟶ X) side.down z b }
    let sections : ∀ side : family.I₀, F.obj (.op (family.X side)) := fun side =>
      Bool.casesOn (motive := fun choice => F.obj (.op (Bool.casesOn choice Z X')))
        side.down centerSection blowUpSection
    have hcompatible : Presieve.Arrows.Compatible F family.f sections := by
      rintro ⟨side⟩ ⟨other⟩ source first second hcomp
      cases side <;> cases other
      · obtain rfl : first = second := (cancel_mono z).mp hcomp
        rfl
      · exact map_eq_map_of_comp_eq B S hS F hSquareSite hsections first second hcomp
      · exact (map_eq_map_of_comp_eq B S hS F hSquareSite hsections second first hcomp.symm).symm
      · exact map_eq_of_comp_blowUp_eq B S hS F hF b z p e hSquareSite U hU
          centerSection blowUpSection hsections first second hcomp
    have hsheaf : Presieve.IsSheafFor F family.presieve₀ := (Presieve.isSheafFor_iff_generate _).2
      (hF.isSheafFor _ (two_arrows_sieve_mem_topology B S hS z b hcover))
    obtain ⟨globalSection, hsection, _⟩ :=
      ((Presieve.isSheafFor_arrows_iff F family.f).mp hsheaf) sections hcompatible
    exact ⟨globalSection, hsection ⟨false⟩, hsection ⟨true⟩⟩

end BigPHOver

end AlgebraicGeometry

end
