module

public import Mathlib.CategoryTheory.Limits.FullSubcategory
public import StacksFrontier.AlgebraicGeometry.Topologies.AffineCreatesPullbacks
public import StacksFrontier.AlgebraicGeometry.Morphisms.FinitePresentation.Diagonal
public import StacksFrontier.AlgebraicGeometry.Thickenings
public import StacksFrontier.AlgebraicGeometry.Morphisms.ProperComplementExtension
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.AlmostBlowUp.IsomorphismAwayFromCenter
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf.FibreProducts
public import StacksFrontier.AlgebraicGeometry.Topologies.HTopology.CoveringRefinement
public import StacksFrontier.AlgebraicGeometry.Topologies.HTopology.SiteCoverings
public import StacksFrontier.CategoryTheory.Sites.Pretopology.TautologicalRelaxed
public import StacksCore.Tactic.StacksAttribute

/-!
# Descent for almost blowup squares in the h topology

An almost blowup square consists of a finitely presented closed centre `Z ⊆ X`, a proper
finitely presented modification `b : X' ⟶ X` which is the blowup of the centre away from its
supported sections, and the exceptional subscheme `E = Z ×_X X'`.  Both the centre and the
modification are proper and of finite presentation, and together they cover `X`, so the two of
them form an h covering of `X`; the fibre products of that covering are in turn covered by the
exceptional subscheme and by the diagonal of the modification.  Consequently a sheaf for the h
topology turns an almost blowup square into a cartesian square of sets: a section over the
centre and a section over the modification agreeing on the exceptional subscheme glue uniquely
to a section over the base.

## Main results

* `AlgebraicGeometry.isPullback_of_almostBlowUpSquare_bigH`: a sheaf on the big h site over a
  scheme sends an almost blowup square to a cartesian square of sets.
* `AlgebraicGeometry.isPullback_of_almostBlowUpSquare_bigAffineH`: the same holds on the big
  affine h site over a scheme.
* `AlgebraicGeometry.bijective_map_of_isThickening_bigH` and
  `AlgebraicGeometry.bijective_map_of_isThickening_bigAffineH`: a sheaf for the h topology
  restricts bijectively along a thickening of finite presentation.

## Implementation notes

The square is presented by its four morphisms in the site together with an ideal sheaf on the
base, the hypothesis that the ideal sheaf and the modification form an almost blowup square,
an identification of the centre with the closed subscheme cut out by the ideal sheaf in the
category of schemes over the base, and the requirement that the square of underlying schemes
be cartesian; the upper-left corner is then the exceptional inverse-image subscheme.  Only an
identification over the base is asked for, so any presentation of the centre available in the
site may be used.

On the big site the two covering families are h coverings of objects of the site and the sheaf
condition is transported to them from a chosen covering family of the site using Stacks 0EU0.
On the affine site the covering families are in addition standard h coverings, which is what
the affine site's covering families are, and the comparison is again Stacks 0EU0 followed by
the invariance of the sheaf condition under tautological equivalence.  The affine site has
pullbacks because its inclusion into the big site creates them, affineness being stable under
fibre products.

A thickening of finite presentation is a proper surjection of finite presentation, hence an h
covering all by itself, and it is a monomorphism, so every section over its source is
compatible for that covering; the sheaf condition therefore says exactly that restriction
along it is bijective.

## References

* [Stacks Project, Tag 0EVD](https://stacks.math.columbia.edu/tag/0EVD)
* [Stacks Project, Tag 0EVE](https://stacks.math.columbia.edu/tag/0EVE)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.Thickenings

universe u v w

namespace AlgebraicGeometry

/-- A family of morphisms locally of finite presentation whose disjoint-union morphism is an h
covering is itself an h covering. -/
private theorem isHCovering_of_sigmaDesc
    {T : Scheme.{u}} {I : Type v} [Small.{u} I]
    (X : I → Scheme.{u}) (f : ∀ i, X i ⟶ T)
    (hlfp : ∀ i, LocallyOfFinitePresentation (f i))
    (hSigma : IsHCovering (fun _ : Unit ↦ ∐ X)
      (fun _ ↦ Sigma.desc f)) :
    IsHCovering X f :=
  (isHCovering_tfae X f hlfp).out 1 3 |>.mpr hSigma

/-- A commuting square of sets is cartesian as soon as every pair of sections agreeing on the
upper-left corner glues uniquely to a section over the lower-right corner. -/
private theorem isPullback_of_unique_gluing
    {C : Type v} [Category.{u, v} C] {E Z X' X : C}
    (F : Cᵒᵖ ⥤ Type w) (e : E ⟶ Z) (p : E ⟶ X') (z : Z ⟶ X) (b : X' ⟶ X)
    (hSquare : e ≫ z = p ≫ b)
    (hGlue : ∀ (sZ : F.obj (op Z)) (sX' : F.obj (op X')),
      F.map e.op sZ = F.map p.op sX' →
        ∃! sX : F.obj (op X),
          F.map z.op sX = sZ ∧ F.map b.op sX = sX') :
    IsPullback (F.map z.op) (F.map b.op) (F.map e.op) (F.map p.op) := by
  have hComm : F.map z.op ≫ F.map e.op = F.map b.op ≫ F.map p.op := by
    rw [← Functor.map_comp, ← Functor.map_comp]
    congr 1
    exact congrArg Quiver.Hom.op hSquare
  let c : PullbackCone (F.map e.op) (F.map p.op) :=
    PullbackCone.mk (F.map z.op) (F.map b.op) hComm
  let glueAt (s : PullbackCone (F.map e.op) (F.map p.op)) (x : s.pt) :=
    hGlue (s.fst x) (s.snd x)
      (congrArg (fun f : TypeCat.Fun _ _ => f x)
        (congrArg ConcreteCategory.hom s.condition))
  exact IsPullback.of_isLimit (c := c) (PullbackCone.IsLimit.mk hComm
    (fun s => TypeCat.ofHom fun x => (glueAt s x).choose)
    (by
      intro s
      ext x
      exact (glueAt s x).choose_spec.1.1)
    (by
      intro s
      ext x
      exact (glueAt s x).choose_spec.1.2)
    (by
      intro s m hm₁ hm₂
      ext x
      apply (glueAt s x).choose_spec.2
      constructor
      · exact congrArg (fun f : TypeCat.Fun _ _ => f x)
          (congrArg ConcreteCategory.hom hm₁)
      · exact congrArg (fun f : TypeCat.Fun _ _ => f x)
          (congrArg ConcreteCategory.hom hm₂)))

/-- Restricting a section along a composite is restricting it along the two factors in turn. -/
private theorem presheaf_map_comp_apply
    {C : Type v} [Category.{u, v} C] {F : Cᵒᵖ ⥤ Type w}
    {A B D : C} (f : A ⟶ B) (g : B ⟶ D) (x : F.obj (op D)) :
    F.map f.op (F.map g.op x) = F.map (f ≫ g).op x := by
  rw [op_comp, FunctorToTypes.map_comp_apply]

/-- A sheaf on the big h site over a scheme satisfies the sheaf condition for every family of
morphisms in the site whose underlying family of scheme morphisms is an h covering and whose
index type is equivalent to one in the site's index universe. -/
private theorem bigH_isSheafFor_of_hCover
    (B : BigHSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : (BigHOver B S hS)ᵒᵖ ⥤ Type v)
    (hF : Presheaf.IsSheaf (BigHOver.topology B S hS) F)
    {X : BigHOver B S hS} (E : PreZeroHypercover X)
    {ι : Type (u + 1)} (ε : ι ≃ E.I₀)
    (hE : IsHCovering
      (E.map (BigHOver.toScheme B S hS)).X
      (E.map (BigHOver.toScheme B S hS)).f) :
    Presieve.IsSheafFor F E.presieve₀ := by
  let K := BigHOver.forget B S hS
  let E' := E.map K
  have hE' : IsHCovering (E'.map B.inclusion).X (E'.map B.inclusion).f := by
    convert hE using 1 <;>
      simp [E', K, BigHOver.toScheme, PreZeroHypercover.map,
        Functor.comp_map]
  let W : PreZeroHypercover.{u + 1} X.left := E'.reindex ε
  have hW : IsHCoveringInCutoff (κ := B.cutoff) ⟨X.left, W⟩ := hE'.reindex ε
  obtain ⟨⟨T', V⟩, hV, hT, hcomb⟩ := B.covering_representative ⟨X.left, W⟩ hW
  cases hT
  have hWV : W.presieve₀ = V.presieve₀ :=
    PreZeroHypercover.presieve₀_eq_of_combinatoriallyEquivalent hcomb
  have hE'V : E'.presieve₀ = V.presieve₀ := by
    rw [← hWV]
    exact (PreZeroHypercover.presieve₀_reindex E' ε).symm
  have hVmem : V.presieve₀ ∈ B.precoverage X.left := ⟨V, rfl, hV⟩
  have hE'sieve : Sieve.generate E'.presieve₀ ∈ B.topology X.left := by
    rw [hE'V]
    exact B.precoverage.generate_mem_toGrothendieck hVmem
  have hgen : Sieve.generate E.presieve₀ ∈ BigHOver.topology B S hS X := by
    rw [BigHOver.topology, GrothendieckTopology.mem_over_iff]
    rw [Sieve.overEquiv_generate]
    apply B.topology.superset_covering _ hE'sieve
    rw [Sieve.generate_le_iff]
    rintro Y f ⟨i⟩
    exact ⟨E'.X i, 𝟙 _, E'.f i,
      ⟨E.X i, E.f i, 𝟙 _, ⟨i⟩, by simp [E', K, PreZeroHypercover.map]⟩,
      by simp⟩
  rw [Presieve.isSheafFor_iff_generate]
  exact hF.isSheafFor _ hgen

/-- The two-element family of objects with members `A` and `B`. -/
private abbrev pairObjects {C : Type v} [Category.{u, v} C] (A B : C) :
    Bool → C
  | false => A
  | true => B

/-- The two-element family of morphisms to a common target with members `f` and `g`. -/
private abbrev pairArrows {C : Type v} [Category.{u, v} C] {A B X : C}
    (f : A ⟶ X) (g : B ⟶ X) :
    (i : Bool) → pairObjects A B i ⟶ X
  | false => f
  | true => g

/-- The two-element family of sections of a presheaf with members `sA` and `sB`. -/
private abbrev pairSections {C : Type v} [Category.{u, v} C]
    {F : Cᵒᵖ ⥤ Type w} {A B : C}
    (sA : F.obj (op A)) (sB : F.obj (op B)) :
    (i : Bool) → F.obj (op (pairObjects A B i))
  | false => sA
  | true => sB

/-- The coproduct of a family indexed by `Bool` is the binary coproduct of its two members. -/
private noncomputable def boolCoproductIso {C : Type v} [Category.{u, v} C]
    (Y : Bool → C) [HasBinaryCoproduct (Y false) (Y true)] [HasCoproduct Y] :
    (∐ Y) ≅ Y false ⨿ Y true where
  hom := Sigma.desc fun i => match i with
    | false => (Limits.coprod.inl : Y false ⟶ Y false ⨿ Y true)
    | true => (Limits.coprod.inr : Y true ⟶ Y false ⨿ Y true)
  inv := Limits.coprod.desc (Sigma.ι Y false) (Sigma.ι Y true)
  hom_inv_id := by
    apply Sigma.hom_ext
    intro i
    cases i with
    | false =>
        symm
        rw [← Category.assoc, Sigma.ι_desc, Limits.coprod.inl_desc]
        simp
    | true =>
        symm
        rw [← Category.assoc, Sigma.ι_desc, Limits.coprod.inr_desc]
        simp
  inv_hom_id := by
    apply Limits.coprod.hom_ext
    · calc
        _ = (Limits.coprod.inl ≫
            Limits.coprod.desc (Sigma.ι Y false) (Sigma.ι Y true)) ≫
              (Sigma.desc fun i => match i with
                | false => (Limits.coprod.inl : Y false ⟶ Y false ⨿ Y true)
                | true => (Limits.coprod.inr : Y true ⟶ Y false ⨿ Y true)) :=
              (Category.assoc _ _ _).symm
        _ = Sigma.ι Y false ≫ (Sigma.desc fun i => match i with
                | false => (Limits.coprod.inl : Y false ⟶ Y false ⨿ Y true)
                | true => (Limits.coprod.inr : Y true ⟶ Y false ⨿ Y true)) := by
              rw [Limits.coprod.inl_desc]
        _ = Limits.coprod.inl := by rw [Sigma.ι_desc]
        _ = Limits.coprod.inl ≫ 𝟙 (Y false ⨿ Y true) := by simp
    · calc
        _ = (Limits.coprod.inr ≫
            Limits.coprod.desc (Sigma.ι Y false) (Sigma.ι Y true)) ≫
              (Sigma.desc fun i => match i with
                | false => (Limits.coprod.inl : Y false ⟶ Y false ⨿ Y true)
                | true => (Limits.coprod.inr : Y true ⟶ Y false ⨿ Y true)) :=
              (Category.assoc _ _ _).symm
        _ = Sigma.ι Y true ≫ (Sigma.desc fun i => match i with
                | false => (Limits.coprod.inl : Y false ⟶ Y false ⨿ Y true)
                | true => (Limits.coprod.inr : Y true ⟶ Y false ⨿ Y true)) := by
              rw [Limits.coprod.inr_desc]
        _ = Limits.coprod.inr := by rw [Sigma.ι_desc]
        _ = Limits.coprod.inr ≫ 𝟙 (Y false ⨿ Y true) := by simp

/-- The morphism out of a disjoint union induced by a family of morphisms locally of finite
presentation is locally of finite presentation. -/
private theorem locallyOfFinitePresentation_sigmaDesc
    {ι : Type v} {X : Scheme.{u}} {Y : ι → Scheme.{u}}
    (f : ∀ i, Y i ⟶ X) [Small.{u} ι]
    (hfp : ∀ i, LocallyOfFinitePresentation (f i)) :
    LocallyOfFinitePresentation (Sigma.desc f) := by
  let : HasRingHomProperty @LocallyOfFinitePresentation RingHom.FinitePresentation := inferInstance
  let : IsZariskiLocalAtSource @LocallyOfFinitePresentation :=
    HasRingHomProperty.instIsZariskiLocalAtSource
      (P := @LocallyOfFinitePresentation) (Q := RingHom.FinitePresentation)
  exact IsZariskiLocalAtSource.sigmaDesc (P := @LocallyOfFinitePresentation) hfp

/-- A two-element family of proper morphisms locally of finite presentation whose images cover
the target is an h covering. -/
private theorem isHCovering_bool_of_range_union
    {X : Scheme.{u}} (Y : Bool → Scheme.{u}) (f : ∀ i, Y i ⟶ X)
    (hfp : ∀ i, LocallyOfFinitePresentation (f i))
    (hproper : ∀ i, IsProper (f i))
    (hrange : Set.range (f false) ∪ Set.range (f true) = Set.univ) :
    IsHCovering Y f := by
  let q := Sigma.desc f
  have hsurj : Surjective q := by
    apply Surjective.sigmaDesc_of_union_range_eq_univ
    have hr : (⋃ i : Bool, Set.range (f i)) =
        Set.range (f false) ∪ Set.range (f true) := by
      ext x
      simp
    rwa [hr]
  have hproperq : IsProper q := by
    let eY := boolCoproductIso Y
    have hfactor : q = eY.hom ≫ Limits.coprod.desc (f false) (f true) := by
      apply Sigma.hom_ext
      intro i
      cases i with
      | false =>
          calc
            Sigma.ι Y false ≫ q = f false := by simp [q]
            _ = Sigma.ι Y false ≫ (eY.hom ≫ Limits.coprod.desc (f false) (f true)) := by
              rw [← Category.assoc]
              dsimp [eY, boolCoproductIso]
              rw [Sigma.ι_desc, Limits.coprod.inl_desc]
      | true =>
          calc
            Sigma.ι Y true ≫ q = f true := by simp [q]
            _ = Sigma.ι Y true ≫ (eY.hom ≫ Limits.coprod.desc (f false) (f true)) := by
              rw [← Category.assoc]
              dsimp [eY, boolCoproductIso]
              rw [Sigma.ι_desc, Limits.coprod.inr_desc]
    let : IsProper (f false) := hproper false
    let : IsProper (f true) := hproper true
    rw [hfactor]
    let : IsProper (Limits.coprod.desc (f false) (f true)) :=
      isProper_coprodDesc (f false) (f true)
    let : IsProper eY.hom := inferInstance
    infer_instance
  have hfpq : FinitePresentation q :=
    ⟨locallyOfFinitePresentation_sigmaDesc f hfp, inferInstance, inferInstance⟩
  exact isHCovering_of_sigmaDesc Y f hfp
    (surjective_proper_isHCovering q hfpq)

/-- Two proper morphisms of finite presentation whose images cover the target form an h
covering. -/
private theorem isHCovering_pair_of_range_union
    {X A B : Scheme.{u}} [Small.{u} Bool]
    (f : A ⟶ X) (g : B ⟶ X)
    (hfp₁ : LocallyOfFinitePresentation f) (hfp₂ : LocallyOfFinitePresentation g)
    [IsProper f] [IsProper g]
    (hrange : Set.range f ∪ Set.range g = Set.univ) :
    IsHCovering (pairObjects A B) (pairArrows f g) :=
  isHCovering_bool_of_range_union _ _ (fun i => by cases i <;> assumption)
    (fun i => by cases i <;> infer_instance) hrange

/-- A two-element family of proper morphisms of finite presentation whose images cover the target
is an h covering. -/
private theorem isHCovering_bool_of_pair_facts
    {X : Scheme.{u}} {Y : Bool → Scheme.{u}} (f : ∀ i, Y i ⟶ X)
    (hfp₀ : FinitePresentation (f false)) (hfp₁ : FinitePresentation (f true))
    (hp₀ : IsProper (f false)) (hp₁ : IsProper (f true))
    (hrange : Set.range (f false) ∪ Set.range (f true) = Set.univ) :
    IsHCovering Y f :=
  isHCovering_bool_of_range_union Y f (fun i => by cases i; exacts [hfp₀.1, hfp₁.1])
    (fun i => by cases i; exacts [hp₀, hp₁]) hrange

/-- A two-element family of proper morphisms of finite presentation between affine schemes whose
images cover the target is a standard h covering. -/
private theorem isStandardHCovering_bool_of_pair_facts
    {X : Scheme.{u}} [IsAffine X] {Y : Bool → Scheme.{u}} (f : ∀ i, Y i ⟶ X)
    (haffine : ∀ i, IsAffine (Y i))
    (hfp₀ : FinitePresentation (f false)) (hfp₁ : FinitePresentation (f true))
    (hp₀ : IsProper (f false)) (hp₁ : IsProper (f true))
    (hrange : Set.range (f false) ∪ Set.range (f true) = Set.univ) :
    IsStandardHCovering f :=
  isStandardHCovering_of_isHCovering (Finite.of_fintype Bool) haffine
    (fun i => by cases i; exacts [hfp₀, hfp₁])
    (isHCovering_bool_of_pair_facts f hfp₀ hfp₁ hp₀ hp₁ hrange)

/-- A point of the fibre square of a morphism lying over an open on which the morphism
restricts to an isomorphism is in the image of the diagonal. -/
private theorem range_diagonal_of_isIso_restrict
    {X Y : Scheme.{u}} (f : X ⟶ Y) (U : Y.Opens)
    (hIso : IsIso (f ∣_ U)) :
    (x : {y : ↑(pullback f f) // (pullback.fst f f ≫ f) y ∈ U}) →
      x.1 ∈ Set.range (pullback.diagonal f) := by
  classical
  let V : X.Opens := f ⁻¹ᵁ U
  let j : V.toScheme ⟶ X := V.ι
  let g : V.toScheme ⟶ U.toScheme := f ∣_ U
  let q : Scheme.{u} := pullback g g
  let k : U.toScheme ⟶ Y := U.ι
  have h₁ : g ≫ k = j ≫ f := by
    dsimp [g, k, j]
    exact morphismRestrict_ι f U
  let a : q ⟶ pullback f f :=
    pullback.map g g f f j j k h₁ h₁
  let : IsIso g := hIso
  let : IsIso (pullback.diagonal g) := by infer_instance
  have hdiag : pullback.diagonal g ≫ a = j ≫ pullback.diagonal f := by
    apply pullback.hom_ext
    · dsimp [a, pullback.map]
      calc
        _ = pullback.diagonal g ≫ (pullback.fst g g ≫ j) := by
          rw [Category.assoc, pullback.lift_fst]
        _ = (pullback.diagonal g ≫ pullback.fst g g) ≫ j := by rw [← Category.assoc]
        _ = j := by rw [pullback.diagonal_fst, Category.id_comp]
        _ = (j ≫ pullback.diagonal f) ≫ pullback.fst f f := by
          rw [Category.assoc, pullback.diagonal_fst, Category.comp_id]
    · dsimp [a, pullback.map]
      calc
        _ = pullback.diagonal g ≫ (pullback.snd g g ≫ j) := by
          rw [Category.assoc, pullback.lift_snd]
        _ = (pullback.diagonal g ≫ pullback.snd g g) ≫ j := by rw [← Category.assoc]
        _ = j := by rw [pullback.diagonal_snd, Category.id_comp]
        _ = (j ≫ pullback.diagonal f) ≫ pullback.snd f f := by
          rw [Category.assoc, pullback.diagonal_snd, Category.comp_id]
  intro x
  have hbase₁ : f (pullback.fst f f x.1) ∈ U := by
    show (pullback.fst f f ≫ f) x.1 ∈ U
    exact x.2
  have hbase₂ : f (pullback.snd f f x.1) ∈ U := by
    have heq := congrArg (fun k : pullback f f ⟶ Y => k x.1) pullback.condition
    change f (pullback.fst f f x.1) = f (pullback.snd f f x.1) at heq
    rw [← heq]
    exact hbase₁
  have hx₁ : pullback.fst f f x.1 ∈ Set.range j :=
    ⟨⟨pullback.fst f f x.1, hbase₁⟩, rfl⟩
  have hx₂ : pullback.snd f f x.1 ∈ Set.range j :=
    ⟨⟨pullback.snd f f x.1, hbase₂⟩, rfl⟩
  have hxmap : x.1 ∈ Set.range a := by
    have haux : x.1 ∈ Set.range
        (pullback.map g g f f j j k h₁ h₁) := by
      rw [Scheme.Pullback.range_map]
      exact ⟨hx₁, hx₂⟩
    simpa only [a] using haux
  obtain ⟨t, ht⟩ := hxmap
  obtain ⟨v, hv⟩ := (pullback.diagonal g).surjective t
  refine ⟨j v, ?_⟩
  have heq : (pullback.diagonal f) (j v) = x.1 := by
    calc
      (pullback.diagonal f) (j v) = (pullback.diagonal g ≫ a) v := by
        rw [hdiag]
        rfl
      _ = a t := by
        show a ((pullback.diagonal g) v) = a t
        rw [hv]
      _ = x.1 := ht
  exact heq

/-- An identification of the centre with the closed subscheme cut out by an ideal sheaf is an
isomorphism of sources over the base. -/
private theorem exists_isIso_comp_subschemeι_eq {X Z : Scheme.{u}} (I : X.IdealSheafData)
    (z : Z ⟶ X) (hZ : Nonempty (Over.mk z ≅ Over.mk I.subschemeι)) :
    ∃ m : Z ⟶ I.subscheme, IsIso m ∧ m ≫ I.subschemeι = z := by
  obtain ⟨a⟩ := hZ
  exact ⟨a.hom.left, (Over.forget X).map_isIso a.hom, Over.w a.hom⟩

/-- The centre of an almost blowup square is a closed immersion with image the support of the
ideal sheaf. -/
private theorem isClosedImmersion_and_range_center {X Z : Scheme.{u}} (I : X.IdealSheafData)
    (z : Z ⟶ X) (hZ : Nonempty (Over.mk z ≅ Over.mk I.subschemeι)) :
    IsClosedImmersion z ∧ Set.range z = I.support := by
  obtain ⟨m, _, hm⟩ := exists_isIso_comp_subschemeι_eq I z hZ
  subst hm
  exact ⟨inferInstance, by
    rw [range_eq_range_of_surjective _ I.subschemeι m rfl, I.range_subschemeι]⟩

private theorem finitePresentation_center_of_almostBlowUpSquare
    {X X' Z : Scheme.{u}} (I : X.IdealSheafData) (b : X' ⟶ X) (z : Z ⟶ X)
    (hb : IsAlmostBlowUpSquare I b)
    (hZ : Nonempty (Over.mk z ≅ Over.mk I.subschemeι)) : FinitePresentation z := by
  obtain ⟨m, _, hm⟩ := exists_isIso_comp_subschemeι_eq I z hZ
  rw [← hm]
  exact ⟨MorphismProperty.comp_mem @LocallyOfFinitePresentation _ _ inferInstance
      hb.center_finitePresentation.1,
    MorphismProperty.comp_mem @QuasiCompact _ _ inferInstance
      hb.center_finitePresentation.2.1,
    MorphismProperty.comp_mem @QuasiSeparated _ _ inferInstance
      hb.center_finitePresentation.2.2⟩

/-- The centre and the modification of an almost blowup square form an h covering of the base,
and the centre is of finite presentation with image the support of the ideal sheaf. -/
private theorem isHCovering_center_and_modification
    {X X' Z : Scheme.{u}} (I : X.IdealSheafData) (b : X' ⟶ X) (z : Z ⟶ X)
    (hb : IsAlmostBlowUpSquare I b)
    (hZ : Nonempty (Over.mk z ≅ Over.mk I.subschemeι)) :
    IsHCovering (pairObjects Z X') (pairArrows z b) ∧
      FinitePresentation z ∧ Set.range z ∪ Set.range b = Set.univ := by
  have hfpz := finitePresentation_center_of_almostBlowUpSquare I b z hb hZ
  obtain ⟨hcl, hrangeZ⟩ := isClosedImmersion_and_range_center I z hZ
  let U : X.Opens := ⟨I.supportᶜ, I.support.isClosed.isOpen_compl⟩
  have hIso : IsIso (b ∣_ U) := isIso_restrict_compl_support I b hb
  have hrange : Set.range z ∪ Set.range b = Set.univ := by
    apply Set.eq_univ_iff_forall.mpr
    intro x
    by_cases hx : x ∈ I.support
    · exact Or.inl (by rw [hrangeZ]; exact hx)
    · right
      let : IsIso (b ∣_ U) := hIso
      obtain ⟨y, hy⟩ := (b ∣_ U).surjective ⟨x, hx⟩
      refine ⟨y.1, ?_⟩
      have hval := congrArg Subtype.val hy
      simpa only [morphismRestrict_base_coe] using hval
  have : IsProper b := hb.proper
  exact ⟨isHCovering_pair_of_range_union z b hfpz.1 hb.finitePresentation.1 hrange,
    hfpz, hrange⟩

/-- **A two-element family of proper morphisms locally of finite presentation whose images cover
the target is an h covering.** -/
public alias isHCovering_bool_of_isProper_of_range_union := isHCovering_bool_of_range_union

/-- **The centre of an almost blowup square is proper of finite presentation, and its image
together with the image of the modification covers the base.**

These are the geometric facts that make the centre and the modification an h covering of the base.
`AlgebraicGeometry.isHCovering_center_and_modification` says exactly that, but packages the
covering as a family indexed by `Bool` through abbreviations private to this module, so its
conclusion cannot be named elsewhere; a caller outside this module assembles the covering of its
own two-element family from these facts and
`AlgebraicGeometry.isHCovering_bool_of_isProper_of_range_union`. -/
public theorem isProper_finitePresentation_range_union_center_modification
    {X X' Z : Scheme.{u}} (I : X.IdealSheafData) (b : X' ⟶ X) (z : Z ⟶ X)
    (hb : IsAlmostBlowUpSquare I b)
    (hZ : Nonempty (Over.mk z ≅ Over.mk I.subschemeι)) :
    IsProper z ∧ FinitePresentation z ∧ Set.range z ∪ Set.range b = Set.univ := by
  have := (isClosedImmersion_and_range_center I z hZ).1
  exact ⟨inferInstance, (isHCovering_center_and_modification I b z hb hZ).2⟩

/-- **The centre of an almost blowup square is a closed immersion.** It is identified over the
base with the closed subscheme cut out by the ideal sheaf, and that identification is an
isomorphism of the sources. -/
public theorem isClosedImmersion_center_of_almostBlowUpSquare {X Z : Scheme.{u}}
    (I : X.IdealSheafData) (z : Z ⟶ X)
    (hZ : Nonempty (Over.mk z ≅ Over.mk I.subschemeι)) : IsClosedImmersion z :=
  (isClosedImmersion_and_range_center I z hZ).1

/-- The base change of the centre of an almost blowup square along the fibre square of the
modification, together with the diagonal of the modification, form an h covering of that fibre
square by proper morphisms of finite presentation. -/
private theorem isHCovering_pair_of_exceptional_pullbacks
    {X X' Z P T : Scheme.{u}} (I : X.IdealSheafData)
    (b : X' ⟶ X) (z : Z ⟶ X)
    (f₁ f₂ : P ⟶ X') (hP : IsPullback f₁ f₂ b b)
    (m : P ⟶ X) (hm : m = f₁ ≫ b)
    (a : T ⟶ Z) (r : T ⟶ P) (hT : IsPullback a r z m)
    (d : X' ⟶ P) (hd₁ : d ≫ f₁ = 𝟙 X') (hd₂ : d ≫ f₂ = 𝟙 X')
    (hb : IsAlmostBlowUpSquare I b)
    (hZ : Nonempty (Over.mk z ≅ Over.mk I.subschemeι)) :
    IsHCovering (pairObjects T X') (pairArrows r d) ∧
      FinitePresentation r ∧ FinitePresentation d ∧
        IsProper r ∧ IsProper d ∧ Set.range r ∪ Set.range d = Set.univ := by
  have hfpz := finitePresentation_center_of_almostBlowUpSquare I b z hb hZ
  obtain ⟨hcl, hrangeZ⟩ := isClosedImmersion_and_range_center I z hZ
  have hrFP : FinitePresentation r :=
    ⟨MorphismProperty.of_isPullback hT (P := @LocallyOfFinitePresentation) hfpz.1,
      MorphismProperty.of_isPullback hT (P := @QuasiCompact) hfpz.2.1,
      MorphismProperty.of_isPullback hT (P := @QuasiSeparated) hfpz.2.2⟩
  have hdiag : d ≫ hP.isoPullback.hom = pullback.diagonal b := by
    apply pullback.hom_ext
    · rw [Category.assoc, hP.isoPullback_hom_fst, hd₁, pullback.diagonal_fst]
    · rw [Category.assoc, hP.isoPullback_hom_snd, hd₂, pullback.diagonal_snd]
  have hdEq : d = pullback.diagonal b ≫ hP.isoPullback.inv := by
    rw [← hdiag, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  let : IsProper b := hb.proper
  have hdFP : FinitePresentation d := by
    rw [hdEq]
    exact ⟨MorphismProperty.comp_mem @LocallyOfFinitePresentation _ _
        (finitePresentation_diagonal b).1 inferInstance,
      MorphismProperty.comp_mem @QuasiCompact _ _
        (finitePresentation_diagonal b).2.1 inferInstance,
      MorphismProperty.comp_mem @QuasiSeparated _ _
        (finitePresentation_diagonal b).2.2 inferInstance⟩
  have hproperd : IsProper d := by
    rw [hdEq]
    infer_instance
  have hrangeR : Set.range r = m ⁻¹' I.support := by
    rw [← hT.isoPullback_hom_snd]
    show Set.range ((pullback.snd z m) ∘ hT.isoPullback.hom) = _
    rw [Set.range_comp,
      Set.range_eq_univ.mpr
        (ConcreteCategory.bijective_of_isIso hT.isoPullback.hom.base).surjective,
      Set.image_univ, Scheme.Pullback.range_snd, hrangeZ]
  have hbase : hP.isoPullback.hom ≫ pullback.fst b b ≫ b = m := by
    show (hP.isoPullback.hom ≫ pullback.fst b b) ≫ b = m
    rw [hP.isoPullback_hom_fst, hm]
  have hrange : Set.range r ∪ Set.range d = Set.univ := by
    apply Set.eq_univ_iff_forall.mpr
    intro x
    by_cases hx : m x ∈ I.support
    · exact Or.inl (by rw [hrangeR]; exact hx)
    · right
      have hx' : (pullback.fst b b ≫ b) (hP.isoPullback.hom x) ∉ I.support := by
        show (hP.isoPullback.hom ≫ pullback.fst b b ≫ b) x ∉ I.support
        rw [hbase]
        exact hx
      let U : X.Opens := ⟨I.supportᶜ, I.support.isClosed.isOpen_compl⟩
      have hIso : IsIso (b ∣_ U) := isIso_restrict_compl_support I b hb
      have hxU : (pullback.fst b b ≫ b) (hP.isoPullback.hom x) ∈ U := by
        simpa [U] using hx'
      obtain ⟨y, hy⟩ := range_diagonal_of_isIso_restrict b U hIso
        ⟨hP.isoPullback.hom x, hxU⟩
      refine ⟨y, ?_⟩
      have hinj : Function.Injective hP.isoPullback.hom :=
        (ConcreteCategory.bijective_of_isIso hP.isoPullback.hom.base).injective
      apply hinj
      calc
        hP.isoPullback.hom (d y) = (d ≫ hP.isoPullback.hom) y := rfl
        _ = pullback.diagonal b y := congrArg (fun f => f y) hdiag
        _ = hP.isoPullback.hom x := hy
  have : IsProper r :=
    MorphismProperty.of_isPullback hT (P := @IsProper) inferInstance
  let : IsProper d := hproperd
  exact ⟨isHCovering_pair_of_range_union r d hrFP.1 hdFP.1 hrange,
    hrFP, hdFP, inferInstance, inferInstance, hrange⟩

/-- **The exceptional base change and the diagonal of the modification of an almost blowup square
are proper of finite presentation, and their images cover the fibre square of the modification.**

These are the geometric facts that make those two morphisms an h covering of `X' ×_X X'`, which is
what identifies the two restrictions along the two projections of a section over the modification.
`AlgebraicGeometry.isHCovering_pair_of_exceptional_pullbacks` says exactly that, but packages the
covering as a family indexed by `Bool` through abbreviations private to this module, so its
conclusion cannot be named elsewhere; a caller outside this module assembles the covering of its
own two-element family from these facts and
`AlgebraicGeometry.isHCovering_bool_of_isProper_of_range_union`, exactly as a caller of
`AlgebraicGeometry.isProper_finitePresentation_range_union_center_modification` does for the
covering of the base. -/
public theorem isProper_finitePresentation_range_union_exceptional_diagonal
    {X X' Z P T : Scheme.{u}} (I : X.IdealSheafData)
    (b : X' ⟶ X) (z : Z ⟶ X)
    (f₁ f₂ : P ⟶ X') (hP : IsPullback f₁ f₂ b b)
    (m : P ⟶ X) (hm : m = f₁ ≫ b)
    (a : T ⟶ Z) (r : T ⟶ P) (hT : IsPullback a r z m)
    (d : X' ⟶ P) (hd₁ : d ≫ f₁ = 𝟙 X') (hd₂ : d ≫ f₂ = 𝟙 X')
    (hb : IsAlmostBlowUpSquare I b)
    (hZ : Nonempty (Over.mk z ≅ Over.mk I.subschemeι)) :
    FinitePresentation r ∧ FinitePresentation d ∧ IsProper r ∧ IsProper d ∧
      Set.range r ∪ Set.range d = Set.univ :=
  (isHCovering_pair_of_exceptional_pullbacks I b z f₁ f₂ hP m hm a r hT d hd₁ hd₂ hb hZ).2

/-- Two sections of a presheaf agreeing on the upper-left corner of a cartesian square with
monomorphic left edge glue uniquely, provided the presheaf satisfies the sheaf condition both
for the two edges of the square and for a covering of their fibre square. -/
private theorem compatible_sections_of_two_coverings
    {C : Type v} [Category.{u, v} C] [HasPullbacks C]
    {F : Cᵒᵖ ⥤ Type w} {Z X' X E T : C}
    (z : Z ⟶ X) (b : X' ⟶ X) (e : E ⟶ Z) (p : E ⟶ X')
    (hSquare : IsPullback e p z b)
    [Mono z]
    (r : T ⟶ pullback b b) (d : X' ⟶ pullback b b)
    (a₁ a₂ : T ⟶ E)
    (hr₁ : r ≫ pullback.fst b b = a₁ ≫ p)
    (hr₂ : r ≫ pullback.snd b b = a₂ ≫ p)
    (he : a₁ ≫ e = a₂ ≫ e)
    (hd₁ : d ≫ pullback.fst b b = 𝟙 X')
    (hd₂ : d ≫ pullback.snd b b = 𝟙 X')
    (sZ : F.obj (op Z)) (sX' : F.obj (op X'))
    (hQ : Presieve.IsSheafFor F (Presieve.ofArrows
      (pairObjects Z X') (pairArrows z b)))
    (hR : Presieve.IsSheafFor F (Presieve.ofArrows
      (pairObjects T X') (pairArrows r d)))
    (hMatch : F.map e.op sZ = F.map p.op sX') :
    ∃! sX : F.obj (op X),
      F.map z.op sX = sZ ∧ F.map b.op sX = sX' := by
  let q := pairObjects Z X'
  let f := pairArrows z b
  let s := pairSections sZ sX'
  let rX := pairObjects T X'
  let rf := pairArrows r d
  have hBB : F.map (pullback.fst b b).op sX' =
      F.map (pullback.snd b b).op sX' := by
    let q₁ := F.map (pullback.fst b b).op sX'
    let q₂ := F.map (pullback.snd b b).op sX'
    have hRinj := (Presieve.isSheafFor_ofArrows_iff_bijective_toCompabible
      (P := F) (X := rX) (π := rf)).mp hR |>.1
    have hcomp :
        Presieve.Arrows.toCompatible F rf q₁ =
          Presieve.Arrows.toCompatible F rf q₂ := by
      apply Subtype.ext
      funext i
      cases i with
      | false =>
          show F.map r.op q₁ = F.map r.op q₂
          dsimp [q₁, q₂]
          rw [presheaf_map_comp_apply r (pullback.fst b b) sX',
            presheaf_map_comp_apply r (pullback.snd b b) sX', hr₁, hr₂]
          rw [← presheaf_map_comp_apply, ← hMatch, presheaf_map_comp_apply, he,
            ← presheaf_map_comp_apply, hMatch, presheaf_map_comp_apply]
      | true =>
          show F.map d.op q₁ = F.map d.op q₂
          dsimp [q₁, q₂]
          rw [presheaf_map_comp_apply d (pullback.fst b b) sX',
            presheaf_map_comp_apply d (pullback.snd b b) sX', hd₁, hd₂]
    exact hRinj hcomp
  have hcompat : Presieve.Arrows.Compatible F f s := by
    intro i j
    cases i with
    | false =>
      cases j with
      | false =>
        intro Y g₁ g₂ h
        have hmono : g₁ = g₂ := (cancel_mono z).1 h
        exact congrArg (fun g => F.map g.op sZ) hmono
      | true =>
        intro Y g₁ g₂ h
        dsimp [f, s, pairArrows, pairSections, pairObjects] at h ⊢
        let k := hSquare.lift g₁ g₂ h
        have hk₁ : k ≫ e = g₁ := hSquare.lift_fst _ _ _
        have hk₂ : k ≫ p = g₂ := hSquare.lift_snd _ _ _
        show F.map g₁.op sZ = F.map g₂.op sX'
        rw [← hk₁, ← hk₂, ← presheaf_map_comp_apply, hMatch, presheaf_map_comp_apply]
    | true =>
      cases j with
      | false =>
        intro Y g₁ g₂ h
        dsimp [f, s, pairArrows, pairSections, pairObjects] at h ⊢
        let k := hSquare.lift g₂ g₁ h.symm
        have hk₁ : k ≫ e = g₂ := hSquare.lift_fst _ _ _
        have hk₂ : k ≫ p = g₁ := hSquare.lift_snd _ _ _
        show F.map g₁.op sX' = F.map g₂.op sZ
        rw [← hk₁, ← hk₂, ← presheaf_map_comp_apply, ← hMatch, presheaf_map_comp_apply]
      | true =>
        intro Y g₁ g₂ h
        dsimp [f, s, pairArrows, pairSections, pairObjects] at h ⊢
        let k := pullback.lift g₁ g₂ h
        have hk₁ : k ≫ pullback.fst b b = g₁ := pullback.lift_fst _ _ _
        have hk₂ : k ≫ pullback.snd b b = g₂ := pullback.lift_snd _ _ _
        show F.map g₁.op sX' = F.map g₂.op sX'
        rw [← hk₁, ← hk₂, ← presheaf_map_comp_apply, hBB, presheaf_map_comp_apply]
  obtain ⟨sX, hsX, huniq⟩ := (Presieve.isSheafFor_arrows_iff
    (P := F) (π := f)).mp hQ s hcompat
  refine ⟨sX, ?_, ?_⟩
  · exact ⟨hsX false, hsX true⟩
  · exact fun t h' => huniq t fun i => by cases i <;> [exact h'.1; exact h'.2]

/-- A family of morphisms over an affine scheme which is covered, member by member up to
isomorphism over the base, by a standard h covering is itself a standard h covering. -/
private theorem standardH_of_refinement_iso {T : Scheme.{u}} [IsAffine T]
    {F : PreZeroHypercover.{v} T} {G : PreZeroHypercover.{w} T}
    (hF : IsStandardHCovering F.f)
    (α : F.I₀ → G.I₀)
    (hX : ∀ j, F.X j ≅ G.X (α j))
    (hf : ∀ j, (hX j).hom ≫ G.f (α j) = F.f j)
    (hα : Function.Surjective α) : IsStandardHCovering G.f := by
  rcases hF with ⟨hfinite, haffine, hfp, P, hP, ⟨φ⟩⟩
  let : Finite F.I₀ := hfinite
  let hFG : F.Hom G := ⟨α, fun j => (hX j).hom, hf⟩
  have hGaffine : ∀ i, IsAffine (G.X i) := by
    intro i
    obtain ⟨j, rfl⟩ := hα i
    exact IsAffine.of_isIso (hX j).inv
  have hGfp : ∀ i, FinitePresentation (G.f i) := by
    intro i
    obtain ⟨j, rfl⟩ := hα i
    have : IsAffine (G.X (α j)) := hGaffine (α j)
    have hEq : G.f (α j) = (hX j).inv ≫ F.f j := by
      rw [← hf j]
      simp
    have hlfp : LocallyOfFinitePresentation (G.f (α j)) := by
      let : LocallyOfFinitePresentation (F.f j) :=
        (hfp j).locallyOfFinitePresentation
      rw [hEq]
      exact locallyOfFinitePresentation_comp (hX j).inv (F.f j)
    exact FinitePresentation.mk hlfp inferInstance inferInstance
  exact ⟨Finite.of_surjective α hα, hGaffine, hGfp, P, hP,
    ⟨φ.comp hFG⟩⟩

/-- A sheaf on the big affine h site over a scheme satisfies the sheaf condition for every
family of morphisms in the site whose underlying family of scheme morphisms is a standard h
covering. -/
private theorem bigAffineH_isSheafFor_of_standardH
    (B : BigHSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : (BigAffineH B S hS)ᵒᵖ ⥤ Type v)
    (hF : Presheaf.IsSheaf (BigAffineH.topology B S hS) F)
    {X : BigAffineH B S hS} (E : PreZeroHypercover X)
    (hstandard : IsStandardHCovering
      (E.map (BigAffineH.toScheme B S hS)).f) :
    Presieve.IsSheafFor F E.presieve₀ := by
  classical
  let u := BigAffineH.inclusion B S hS
  let K := BigHOver.forget B S hS
  let L := u ⋙ K
  let X' := u.obj X
  let T : B.Schemes := X'.left
  let E' : PreZeroHypercover T := E.map L
  let E₀ := E.map (BigAffineH.toScheme B S hS)
  have : IsAffine (B.inclusion.obj T) := X.property
  have hstandard' : IsStandardHCovering E₀.f := hstandard
  obtain ⟨Q, hQ, htaut⟩ :=
    exists_isCovering_tautologicallyEquivalent_standardHCovering B T E₀ hstandard'
  rcases htaut with ⟨⟨α, hα'⟩, _⟩
  choose e he using hα'
  let I := Set.range α
  let toRange : E₀.I₀ → I := fun k => ⟨α k, ⟨k, rfl⟩⟩
  have hsurj : Function.Surjective toRange := fun i => ⟨i.2.choose, Subtype.ext i.2.choose_spec⟩
  let G : PreZeroHypercover.{u + 1} (B.inclusion.obj T) :=
    ⟨I, fun i => (Q.map B.inclusion).X i.1, fun i => (Q.map B.inclusion).f i.1⟩
  have hGstandard : IsStandardHCovering G.f :=
    standardH_of_refinement_iso hstandard' toRange (fun k => e k)
      (fun k => by simpa [G, toRange] using he k) hsurj
  have hGh : IsHCovering G.X G.f := hGstandard.isHCovering
  let V : PreZeroHypercover.{u + 1} T :=
    ⟨I, fun i => Q.X i.1, fun i => Q.f i.1⟩
  have hVcover : B.IsCovering ⟨T, V⟩ :=
    ⟨hGh, (Cardinal.mk_le_of_injective Subtype.val_injective).trans hQ.2⟩
  let Vobj (i : I) : BigAffineH B S hS :=
    { obj := Over.mk (Q.f i.1 ≫ X'.hom)
      property := hGstandard.2.1 i }
  let vmap (i : I) : u.obj (Vobj i) ⟶ X' := Over.homMk (Q.f i.1)
  let D : PreZeroHypercover X :=
    ⟨I, fun i => Vobj i, fun i => ObjectProperty.homMk (vmap i)⟩
  have hDcover : BigAffineH.IsCovering B S hS ⟨X, D⟩ := ⟨hVcover, hGstandard⟩
  have hDgen : Sieve.generate D.presieve₀ ∈ BigAffineH.topology B S hS X :=
    Precoverage.generate_mem_toGrothendieck ⟨D, rfl, hDcover⟩
  have hD : Presieve.IsSheafFor F D.presieve₀ := by
    rw [Presieve.isSheafFor_iff_generate]
    exact hF.isSheafFor _ hDgen
  let α' : E.I₀ → I := toRange
  let eover (k : E.I₀) : E.X k ≅ D.X (α' k) := by
    let eB : (u.obj (E.X k)).left ≅ (u.obj (D.X (α' k))).left := by
      show E'.X k ≅ Q.X (α k)
      exact B.inclusion.preimageIso (e k)
    have hmap : B.inclusion.map eB.hom = (e k).hom := by
      dsimp [eB]
      exact B.inclusion.map_preimage (e k).hom
    have hbase : eB.hom ≫ (u.obj (D.X (α' k))).hom =
        (u.obj (E.X k)).hom := by
      apply B.inclusion.map_injective
      show B.inclusion.map eB.hom ≫
          B.inclusion.map ((u.obj (D.X (α' k))).hom) =
        B.inclusion.map ((u.obj (E.X k)).hom)
      rw [hmap]
      show (e k).hom ≫ B.inclusion.map (Q.f (α k) ≫ X'.hom) =
        B.inclusion.map (u.obj (E.X k)).hom
      rw [Functor.map_comp]
      show ((e k).hom ≫ (Q.map B.inclusion).f (α k)) ≫
        B.inclusion.map X'.hom = _
      rw [he k]
      show B.inclusion.map (u.map (E.f k)).left ≫ B.inclusion.map X'.hom = _
      rw [← Functor.map_comp, Over.w]
    let eO : u.obj (E.X k) ≅ u.obj (D.X (α' k)) := Over.isoMk eB hbase
    exact u.preimageIso eO
  have htri (k : E.I₀) : (eover k).hom ≫ D.f (α' k) = E.f k := by
    apply u.map_injective
    simp only [Functor.map_comp, eover, Functor.preimageIso_hom,
      Functor.map_preimage]
    apply K.map_injective
    apply B.inclusion.map_injective
    show B.inclusion.map ((B.inclusion.preimageIso (e k)).hom ≫ Q.f (α k)) =
      B.inclusion.map (u.map (E.f k)).left
    show B.inclusion.map (B.inclusion.preimage (e k).hom) ≫
      B.inclusion.map (Q.f (α k)) = _
    rw [B.inclusion.map_preimage (e k).hom]
    exact he k
  have htautED : PreZeroHypercover.TautologicallyEquivalent E D := by
    refine ⟨⟨α', fun k => ⟨eover k, htri k⟩⟩, ?_⟩
    refine ⟨(fun i => i.2.choose), ?_⟩
    intro i
    let k : E.I₀ := i.2.choose
    have hk : α' k = i := Subtype.ext i.2.choose_spec
    let αiso := eqToIso (congrArg D.X hk)
    refine ⟨αiso.symm ≪≫ (eover k).symm, ?_⟩
    calc
      (αiso.symm ≪≫ (eover k).symm).hom ≫ E.f k =
          αiso.inv ≫ (eover k).symm.hom ≫ E.f k := Category.assoc _ _ _
      _ = αiso.inv ≫ D.f (α' k) := by
            rw [← htri k]
            simp
      _ = D.f i := by
            simpa [αiso] using
              (eqToHom_naturality (fun j => D.f j) hk.symm).symm
  exact (PreZeroHypercover.isSheafFor_presieve₀_iff_of_tautologicallyEquivalent
    E D htautED F).mpr hD

/-- The inclusion of the big affine h site over a scheme into the big h site over it creates
pullbacks. -/
private noncomputable abbrev createsPullbacks_bigAffineH
    (B : BigHSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) :
    CreatesLimitsOfShape WalkingCospan (BigAffineH.inclusion B S hS) :=
  affineCreatesPullbacks (BigHOver.toScheme B S hS)

attribute [local instance] createsPullbacks_bigAffineH

/-- The big affine h site over a scheme has pullbacks. -/
private theorem hasPullbacks_bigAffineH
    (B : BigHSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) :
    HasPullbacks (BigAffineH B S hS) :=
  hasLimitsOfShape_of_hasLimitsOfShape_createsLimitsOfShape
    (BigAffineH.inclusion B S hS)

attribute [local instance] hasPullbacks_bigAffineH

/-- The exceptional base change and the diagonal of the modification of an almost blowup square
are proper of finite presentation, and their images cover the fibre square, for the image under a
pullback-preserving functor to schemes. -/
private theorem exceptional_diagonal_facts {C : Type*} [Category C] [HasPullbacks C]
    (K : C ⥤ Scheme.{u}) [PreservesLimitsOfShape WalkingCospan K]
    {X X' Z : C} (I : (K.obj X).IdealSheafData) (b : X' ⟶ X) (z : Z ⟶ X)
    (hb : IsAlmostBlowUpSquare I (K.map b))
    (hZ : Nonempty (Over.mk (K.map z) ≅ Over.mk I.subschemeι)) :
    FinitePresentation (K.map (pullback.snd z (pullback.fst b b ≫ b))) ∧
      FinitePresentation (K.map (pullback.diagonal b)) ∧
      IsProper (K.map (pullback.snd z (pullback.fst b b ≫ b))) ∧
      IsProper (K.map (pullback.diagonal b)) ∧
      Set.range (K.map (pullback.snd z (pullback.fst b b ≫ b))) ∪
        Set.range (K.map (pullback.diagonal b)) = Set.univ :=
  isProper_finitePresentation_range_union_exceptional_diagonal I (K.map b) (K.map z)
    (K.map (pullback.fst b b)) (K.map (pullback.snd b b)) ((IsPullback.of_hasPullback b b).map K)
    (K.map (pullback.fst b b ≫ b)) (K.map_comp _ _) (K.map (pullback.fst z _)) _
    ((IsPullback.of_hasPullback z _).map K) (K.map (pullback.diagonal b))
    (by rw [← K.map_comp]; simp) (by rw [← K.map_comp]; simp) hb hZ

/-- A presheaf satisfying the sheaf condition for the centre and modification of a pullback square
with monomorphic centre, and for the base change of the centre along the fibre square of the
modification together with the diagonal, sends the square to a cartesian square of sets. -/
private theorem isPullback_of_isSheafFor_pair_coverings
    {C : Type v} [Category.{u, v} C] [HasPullbacks C] {F : Cᵒᵖ ⥤ Type w} {Z X' X E : C}
    (z : Z ⟶ X) (b : X' ⟶ X) (e : E ⟶ Z) (p : E ⟶ X') (hSquare : IsPullback e p z b) [Mono z]
    (hQ : Presieve.IsSheafFor F (Presieve.ofArrows (pairObjects Z X') (pairArrows z b)))
    (hR : Presieve.IsSheafFor F (Presieve.ofArrows
      (pairObjects (pullback z (pullback.fst b b ≫ b)) X')
      (pairArrows (pullback.snd z (pullback.fst b b ≫ b)) (pullback.diagonal b)))) :
    IsPullback (F.map z.op) (F.map b.op) (F.map e.op) (F.map p.op) := by
  have key (k : pullback b b ⟶ X') (hk : k ≫ b = pullback.fst b b ≫ b) :
      ∃ a : pullback z (pullback.fst b b ≫ b) ⟶ E,
        a ≫ e = pullback.fst z _ ∧ a ≫ p = pullback.snd z _ ≫ k :=
    ⟨hSquare.lift _ _ (by rw [Category.assoc, hk]; exact pullback.condition),
      hSquare.lift_fst _ _ _, hSquare.lift_snd _ _ _⟩
  obtain ⟨a₁, ha₁, hp₁⟩ := key (pullback.fst b b) rfl
  obtain ⟨a₂, ha₂, hp₂⟩ := key (pullback.snd b b) pullback.condition.symm
  exact isPullback_of_unique_gluing F e p z b hSquare.w fun sZ sX' hMatch =>
    compatible_sections_of_two_coverings z b e p hSquare _ _ a₁ a₂ hp₁.symm hp₂.symm
      (ha₁.trans ha₂.symm) (by simp) (by simp) sZ sX' hQ hR hMatch

/-- **Stacks 0EVD.** A sheaf on the big h site over a scheme sends an almost blowup square to
a cartesian square of sets. -/
@[stacks 0EVD "big h site"]
public theorem isPullback_of_almostBlowUpSquare_bigH
    (B : BigHSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : (BigHOver B S hS)ᵒᵖ ⥤ Type v)
    (hF : Presheaf.IsSheaf (BigHOver.topology B S hS) F)
    {X X' Z E : BigHOver B S hS}
    (b : X' ⟶ X) (z : Z ⟶ X) (p : E ⟶ X') (e : E ⟶ Z)
    (I : ((BigHOver.toScheme B S hS).obj X).IdealSheafData)
    (hb : IsAlmostBlowUpSquare I ((BigHOver.toScheme B S hS).map b))
    (hZ : Nonempty
      (Over.mk ((BigHOver.toScheme B S hS).map z) ≅
        Over.mk I.subschemeι))
    (hSquare : IsPullback
      ((BigHOver.toScheme B S hS).map e)
      ((BigHOver.toScheme B S hS).map p)
      ((BigHOver.toScheme B S hS).map z)
      ((BigHOver.toScheme B S hS).map b)) :
    IsPullback (F.map z.op) (F.map b.op) (F.map e.op) (F.map p.op) := by
  let K := BigHOver.toScheme B S hS
  have hSquare' : IsPullback e p z b :=
    IsPullback.of_map_of_faithful K hSquare
  let Qcover : PreZeroHypercover X :=
    ⟨Bool, pairObjects Z X', pairArrows z b⟩
  have hQ : Presieve.IsSheafFor F Qcover.presieve₀ := by
    obtain ⟨hproper, hfp, hrange⟩ :=
      isProper_finitePresentation_range_union_center_modification I (K.map b) (K.map z) hb hZ
    have := hb.proper
    exact bigH_isSheafFor_of_hCover B S hS F hF Qcover
      (Equiv.ulift : ULift.{u + 1} Bool ≃ Bool)
      (isHCovering_bool_of_pair_facts _ hfp hb.finitePresentation hproper hb.proper hrange)
  let Rcover : PreZeroHypercover (pullback b b) :=
    ⟨Bool, pairObjects (pullback z (pullback.fst b b ≫ b)) X',
      pairArrows (pullback.snd z (pullback.fst b b ≫ b)) (pullback.diagonal b)⟩
  have hR : Presieve.IsSheafFor F Rcover.presieve₀ := by
    obtain ⟨hfp₀, hfp₁, hp₀, hp₁, hrange⟩ := exceptional_diagonal_facts K I b z hb hZ
    exact bigH_isSheafFor_of_hCover B S hS F hF Rcover
      (Equiv.ulift : ULift.{u + 1} Bool ≃ Bool)
      (isHCovering_bool_of_pair_facts _ hfp₀ hfp₁ hp₀ hp₁ hrange)
  have : Mono z := K.mono_of_mono_map (by
    have := isClosedImmersion_center_of_almostBlowUpSquare I (K.map z) hZ
    exact inferInstanceAs (Mono (K.map z)))
  exact isPullback_of_isSheafFor_pair_coverings z b e p hSquare' hQ hR

/-- **Stacks 0EVD.** A sheaf on the big affine h site over a scheme sends an almost blowup
square to a cartesian square of sets. -/
@[stacks 0EVD "big affine h site"]
public theorem isPullback_of_almostBlowUpSquare_bigAffineH
    (B : BigHSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : (BigAffineH B S hS)ᵒᵖ ⥤ Type v)
    (hF : Presheaf.IsSheaf (BigAffineH.topology B S hS) F)
    {X X' Z E : BigAffineH B S hS}
    (b : X' ⟶ X) (z : Z ⟶ X) (p : E ⟶ X') (e : E ⟶ Z)
    (I : ((BigAffineH.toScheme B S hS).obj X).IdealSheafData)
    (hb : IsAlmostBlowUpSquare I ((BigAffineH.toScheme B S hS).map b))
    (hZ : Nonempty
      (Over.mk ((BigAffineH.toScheme B S hS).map z) ≅
        Over.mk I.subschemeι))
    (hSquare : IsPullback
      ((BigAffineH.toScheme B S hS).map e)
      ((BigAffineH.toScheme B S hS).map p)
      ((BigAffineH.toScheme B S hS).map z)
      ((BigAffineH.toScheme B S hS).map b)) :
    IsPullback (F.map z.op) (F.map b.op) (F.map e.op) (F.map p.op) := by
  let K := BigAffineH.toScheme B S hS
  have hSquare' : IsPullback e p z b :=
    IsPullback.of_map_of_faithful K hSquare
  let Qcover : PreZeroHypercover X :=
    ⟨Bool, pairObjects Z X', pairArrows z b⟩
  have hQ : Presieve.IsSheafFor F Qcover.presieve₀ := by
    obtain ⟨hproper, hfp, hrange⟩ :=
      isProper_finitePresentation_range_union_center_modification I (K.map b) (K.map z) hb hZ
    have := hb.proper
    exact bigAffineH_isSheafFor_of_standardH B S hS F hF Qcover
      (isStandardHCovering_bool_of_pair_facts _ (fun i => (Qcover.X i).property) hfp
        hb.finitePresentation hproper hb.proper hrange)
  let Rcover : PreZeroHypercover (pullback b b) :=
    ⟨Bool, pairObjects (pullback z (pullback.fst b b ≫ b)) X',
      pairArrows (pullback.snd z (pullback.fst b b ≫ b)) (pullback.diagonal b)⟩
  have hR : Presieve.IsSheafFor F Rcover.presieve₀ := by
    obtain ⟨hfp₀, hfp₁, hp₀, hp₁, hrange⟩ := exceptional_diagonal_facts K I b z hb hZ
    exact bigAffineH_isSheafFor_of_standardH B S hS F hF Rcover
      (isStandardHCovering_bool_of_pair_facts _ (fun i => (Rcover.X i).property) hfp₀ hfp₁
        hp₀ hp₁ hrange)
  have : Mono z := K.mono_of_mono_map (by
    have := isClosedImmersion_center_of_almostBlowUpSquare I (K.map z) hZ
    exact inferInstanceAs (Mono (K.map z)))
  exact isPullback_of_isSheafFor_pair_coverings z b e p hSquare' hQ hR

/-- A presheaf satisfying the sheaf condition for the one-element family consisting of a
monomorphism restricts bijectively along it: every section over the source is automatically
compatible, hence extends uniquely. -/
private theorem bijective_map_of_isSheafFor_singleton {C : Type*} [Category C]
    {F : Cᵒᵖ ⥤ Type*} {A A' : C} (i : A ⟶ A') [Mono i]
    (hF : Presieve.IsSheafFor F (Presieve.singleton i)) :
    Function.Bijective (F.map i.op) := by
  refine ⟨Presieve.isSeparatedFor_singleton.1 hF.isSeparatedFor, fun x => ?_⟩
  rw [Presieve.isSheafFor_singleton] at hF
  exact (hF x fun p₁ p₂ h => by rw [(cancel_mono i).1 h]).exists

/-- A thickening of finite presentation, read as a one-element family, is an h covering. -/
private theorem isHCovering_singleton_of_isThickening {C : Type*} [Category C]
    (K : C ⥤ Scheme.{u}) {X X' : C} (i : X ⟶ X') (hi : IsThickening (K.map i))
    (hfp : FinitePresentation (K.map i)) :
    IsHCovering ((PreZeroHypercover.singleton.{u + 1} i).map K).X
      ((PreZeroHypercover.singleton.{u + 1} i).map K).f :=
  have := hi.1
  have : Surjective (K.map i) := ⟨hi.2⟩
  (surjective_proper_isHCovering (K.map i) hfp).reindex (Equiv.ofUnique PUnit.{u + 2} Unit)

/-- **Stacks 0EVE.** A sheaf on the big h site over a scheme restricts bijectively along a
morphism of the site which is a thickening and of finite presentation. -/
@[stacks 0EVE "big h site"]
public theorem bijective_map_of_isThickening_bigH
    (B : BigHSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : (BigHOver B S hS)ᵒᵖ ⥤ Type v)
    (hF : Presheaf.IsSheaf (BigHOver.topology B S hS) F)
    {X X' : BigHOver B S hS} (i : X ⟶ X')
    (hi : IsThickening ((BigHOver.toScheme B S hS).map i))
    (hfp : FinitePresentation ((BigHOver.toScheme B S hS).map i)) :
    Function.Bijective (F.map i.op) := by
  have hE := isHCovering_singleton_of_isThickening (BigHOver.toScheme B S hS) i hi hfp
  have := hi.1
  have hFor := bigH_isSheafFor_of_hCover B S hS F hF
    (PreZeroHypercover.singleton.{u + 1} i) (Equiv.refl PUnit.{u + 2}) hE
  rw [PreZeroHypercover.presieve₀_singleton] at hFor
  have : Mono i := (BigHOver.toScheme B S hS).mono_of_mono_map
    (inferInstanceAs (Mono ((BigHOver.toScheme B S hS).map i)))
  exact bijective_map_of_isSheafFor_singleton i hFor

/-- **Stacks 0EVE.** A sheaf on the big affine h site over a scheme restricts bijectively
along a morphism of the site which is a thickening and of finite presentation. -/
@[stacks 0EVE "big affine h site"]
public theorem bijective_map_of_isThickening_bigAffineH
    (B : BigHSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : (BigAffineH B S hS)ᵒᵖ ⥤ Type v)
    (hF : Presheaf.IsSheaf (BigAffineH.topology B S hS) F)
    {X X' : BigAffineH B S hS} (i : X ⟶ X')
    (hi : IsThickening ((BigAffineH.toScheme B S hS).map i))
    (hfp : FinitePresentation ((BigAffineH.toScheme B S hS).map i)) :
    Function.Bijective (F.map i.op) := by
  have hE := isHCovering_singleton_of_isThickening (BigAffineH.toScheme B S hS) i hi hfp
  have := hi.1
  have hstandard : IsStandardHCovering
      ((PreZeroHypercover.singleton.{u + 1} i).map (BigAffineH.toScheme B S hS)).f :=
    isStandardHCovering_of_isHCovering (inferInstanceAs (Finite PUnit.{u + 2}))
      (fun _ => inferInstanceAs (IsAffine ((BigAffineH.toScheme B S hS).obj X)))
      (fun _ => hfp) hE
  have hFor := bigAffineH_isSheafFor_of_standardH B S hS F hF
    (PreZeroHypercover.singleton.{u + 1} i) hstandard
  rw [PreZeroHypercover.presieve₀_singleton] at hFor
  have : Mono i := (BigAffineH.toScheme B S hS).mono_of_mono_map
    (inferInstanceAs (Mono ((BigAffineH.toScheme B S hS).map i)))
  exact bijective_map_of_isSheafFor_singleton i hFor


/-- The centre and the modification of an almost blowup square of the big h site over a scheme,
read as a two-element family of morphisms of schemes, form an h covering of the base.  This is
the covering of Stacks 0EVD, in the form in which a consumer outside this file builds the
corresponding covering sieve of the site. -/
public theorem isHCovering_center_and_modification_bigH
    (B : BigHSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X X' Z : BigHOver B S hS} (b : X' ⟶ X) (z : Z ⟶ X)
    (I : ((BigHOver.toScheme B S hS).obj X).IdealSheafData)
    (hb : IsAlmostBlowUpSquare I ((BigHOver.toScheme B S hS).map b))
    (hZ : Nonempty
      (Over.mk ((BigHOver.toScheme B S hS).map z) ≅ Over.mk I.subschemeι)) :
    IsHCovering (fun i : Bool ↦ (BigHOver.toScheme B S hS).obj (cond i X' Z))
      (fun i ↦ (BigHOver.toScheme B S hS).map
        (Bool.rec (motive := fun j ↦ cond j X' Z ⟶ X) z b i)) := by
  obtain ⟨hproper, hfp, hrange⟩ := isProper_finitePresentation_range_union_center_modification
    I _ _ hb hZ
  exact isHCovering_bool_of_pair_facts _ hfp hb.finitePresentation hproper hb.proper hrange

/-- The base change of the centre of an almost blowup square of the big h site along the fibre
square of the modification, together with the diagonal of the modification, read as a
two-element family of morphisms of schemes, form an h covering of that fibre square.  This is the
second covering of Stacks 0EVD, in the form in which a consumer outside this file builds the
corresponding covering sieve of the site. -/
public theorem isHCovering_exceptional_and_diagonal_bigH
    (B : BigHSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X X' Z : BigHOver B S hS} (b : X' ⟶ X) (z : Z ⟶ X)
    (I : ((BigHOver.toScheme B S hS).obj X).IdealSheafData)
    (hb : IsAlmostBlowUpSquare I ((BigHOver.toScheme B S hS).map b))
    (hZ : Nonempty
      (Over.mk ((BigHOver.toScheme B S hS).map z) ≅ Over.mk I.subschemeι)) :
    IsHCovering
      (fun i : Bool ↦ (BigHOver.toScheme B S hS).obj
        (cond i X' (pullback z (pullback.fst b b ≫ b))))
      (fun i ↦ (BigHOver.toScheme B S hS).map
        (Bool.rec (motive := fun j ↦ cond j X' (pullback z (pullback.fst b b ≫ b)) ⟶
          pullback b b) (pullback.snd z (pullback.fst b b ≫ b)) (pullback.diagonal b) i)) := by
  obtain ⟨hfp₀, hfp₁, hp₀, hp₁, hrange⟩ :=
    exceptional_diagonal_facts (BigHOver.toScheme B S hS) I b z hb hZ
  exact isHCovering_bool_of_pair_facts _ hfp₀ hfp₁ hp₀ hp₁ hrange

end AlgebraicGeometry

end
