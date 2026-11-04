module

public import Mathlib.AlgebraicGeometry.Cover.QuasiCompact
public import Mathlib.CategoryTheory.Sites.PreservesLimits
public import Mathlib.CategoryTheory.Sites.RegularEpi
public import Mathlib.CategoryTheory.Sites.Subcanonical
public import Mathlib.CategoryTheory.Sites.SubcanonicalOver
public import StacksFrontier.CategoryTheory.Sites.Representable.SheafifiedYonedaSubcanonical
public import StacksFrontier.AlgebraicGeometry.FormalSpace.McQuillan
public import StacksFrontier.AlgebraicGeometry.FormalSpace.StageThickening
public import StacksFrontier.AlgebraicGeometry.FormalSpace.WeakIdealPresentation
public import StacksFrontier.AlgebraicGeometry.Spaces.Glueing.SmallSite
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale
public import StacksFrontier.CategoryTheory.Sites.QuasiCompact.ObjectsAndColimits
public import StacksFrontier.RingTheory.Nilpotent.Ideal
public import StacksFrontier.Topology.Algebra.AdicTopology.WeaklyAdmissible
public import StacksFrontier.AlgebraicGeometry.Spaces.Presentation.BigFppfSite

/-!
# Classification of thickenings of a McQuillan affine formal space

For a weakly admissible ring presenting a McQuillan affine formal algebraic
space, its weak ideals of definition classify the representable thickening
morphisms from schemes into that space. The ideal is the kernel of the induced
map from the presenting ring to the scheme's ring of global sections.

## Main definitions

* `quotientMap` is the morphism from a canonical quotient stage to the space.
* `inducedSectionHom` is the homomorphism on global sections attached to a
  representable thickening into the formal space.

## Main results

* `relativelyRepresentable_quotient` and `isThickening_quotient` give the
  representable thickening associated with a weak ideal of definition.
* `existsUnique_weakIdeal_quotient` identifies every such thickening, uniquely,
  with one of these quotient schemes over the formal space.
* `inducedSectionHom_quotient` identifies it at every compatible quotient stage.
* `quotient_ker_sections` recovers the classifying ideal as its kernel.

## Implementation notes

The associated ring is specified by its canonical weak-ideal colimit
presentation. A scheme over the base is an object of the big fppf site. The
classification identifies morphisms up to isomorphism over the formal space,
so the uniqueness statement is uniqueness of the weak ideal rather than of the
isomorphism.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.FormalSpace

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (A : Type u) [CommRing A] [TopologicalSpace A]
  [IsTopologicalRing A] [IsLinearTopology A A]
  (X : FppfSheaf B S hS)
  (P : WeakIdealColimitPresentation B S hS A X)

private theorem quotient_factor_locallyNilpotent
    {R : Type*} [CommRing R] [TopologicalSpace R]
    {I J : Ideal R} (hJI : J ≤ I)
    (hI : TopologicalRing.IsWeakIdealOfDefinition I) (hJopen : IsOpen (J : Set R)) :
    (RingHom.ker (Ideal.Quotient.factor hJI)).LocallyNilpotent := by
  intro x hx
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  have haI : a ∈ I := Ideal.Quotient.eq_zero_iff_mem.mp (by simpa using hx)
  obtain ⟨n, hn⟩ := ((hI.2 a haI).eventually (hJopen.mem_nhds J.zero_mem)).exists
  exact ⟨n, Ideal.Quotient.eq_zero_iff_mem.mpr hn⟩

private theorem quotient_factor_isThickening
    {R : Type*} [CommRing R] [TopologicalSpace R]
    {I J : Ideal R} (hJI : J ≤ I)
    (hI : TopologicalRing.IsWeakIdealOfDefinition I)
    (hJ : TopologicalRing.IsWeakIdealOfDefinition J) :
    Stacks.Thickenings.IsThickening
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor hJI))) := by
  let f := Ideal.Quotient.factor hJI
  have hsurj : Function.Surjective f := Ideal.Quotient.factor_surjective hJI
  have hSpec : Function.Surjective (Spec.map (CommRingCat.ofHom f)) := by
    intro p
    have : p.asIdeal.IsPrime := p.2
    have hkerle : RingHom.ker f ≤ p.asIdeal := by
      intro x hx
      obtain ⟨n, hn⟩ := quotient_factor_locallyNilpotent hJI hI hJ.1 x (by
        simpa [f] using hx)
      exact p.2.mem_of_pow_mem n (hn ▸ Ideal.zero_mem _)
    let q : PrimeSpectrum (R ⧸ I) :=
      ⟨p.asIdeal.map f, Ideal.map_isPrime_of_surjective hsurj hkerle⟩
    refine ⟨q, PrimeSpectrum.ext ?_⟩
    show Ideal.comap f (p.asIdeal.map f) = p.asIdeal
    rw [Ideal.comap_map_of_surjective f hsurj]
    exact sup_eq_left.mpr hkerle
  exact ⟨IsClosedImmersion.spec_of_surjective _ hsurj, hSpec⟩

private theorem weakIdeals_nonempty
    (hA : TopologicalRing.IsWeaklyAdmissible A) :
    Nonempty (WeakIdeals A) :=
  ⟨OrderDual.toDual ⟨Classical.choose hA.1, Classical.choose_spec hA.1⟩⟩

private abbrev LiftedWeakIdealIndex :=
  ULift.{u + 1, u} (WeakIdeals A)

private theorem liftedWeakIdeals_nonempty
    (hA : TopologicalRing.IsWeaklyAdmissible A) :
    Nonempty (LiftedWeakIdealIndex (A := A)) :=
  ⟨ULift.up (Classical.choice (TopologicalRing.nonempty_weakIdealOfDefinitionIndex hA.1))⟩

omit [IsTopologicalRing A] [IsLinearTopology A A] in
private theorem weakIdeals_directed :
    IsDirected (WeakIdeals A) (· ≤ ·) := by
  refine ⟨fun J K => ?_⟩
  refine ⟨OrderDual.toDual ⟨J.1 ⊓ K.1,
    ⟨J.2.1.inter K.2.1, fun x hx => J.2.2 x hx.1⟩⟩, ?_, ?_⟩
  · show J.1 ⊓ K.1 ≤ J.1
    exact inf_le_left
  · show J.1 ⊓ K.1 ≤ K.1
    exact inf_le_right

omit [IsTopologicalRing A] [IsLinearTopology A A] in
private theorem liftedWeakIdeals_directed :
    IsDirected (LiftedWeakIdealIndex (A := A)) (· ≤ ·) := by
  refine ⟨fun i j => ?_⟩
  obtain ⟨k, hik, hjk⟩ :=
    (TopologicalRing.isDirected_weakIdealOfDefinitionIndex A).directed i.down j.down
  exact ⟨ULift.up k, hik, hjk⟩

private def liftedWeakIdealDownFunctor :
    LiftedWeakIdealIndex (A := A) ⥤ WeakIdeals A where
  obj i := i.down
  map {i j} f := homOfLE (show i.down ≤ j.down from (show i ≤ j from leOfHom f))
  map_id _ := Subsingleton.elim _ _
  map_comp _ _ := Subsingleton.elim _ _

omit [IsTopologicalRing A] [IsLinearTopology A A] in
private theorem liftedWeakIdealDownFunctorFull :
    (liftedWeakIdealDownFunctor (A := A)).Full where
  map_surjective {X Y} f :=
    ⟨ULift.up (PLift.up (show X.down ≤ Y.down from leOfHom f)), Subsingleton.elim _ _⟩

attribute [local instance] liftedWeakIdealDownFunctorFull

omit [IsTopologicalRing A] [IsLinearTopology A A] in
private theorem liftedWeakIdealDownFunctorFaithful :
    (liftedWeakIdealDownFunctor (A := A)).Faithful where
  map_injective _ := Subsingleton.elim _ _

attribute [local instance] liftedWeakIdealDownFunctorFaithful

omit [IsTopologicalRing A] [IsLinearTopology A A] in
private theorem liftedWeakIdealDownFunctorFinal :
    Functor.Final (liftedWeakIdealDownFunctor (A := A)) where
  out _d := isConnected_of_isInitial _
    (StructuredArrow.mkIdInitial (T := liftedWeakIdealDownFunctor (A := A)))

attribute [local instance] liftedWeakIdealDownFunctorFinal

private def liftedQuotientDiagram :
    LiftedWeakIdealIndex (A := A) ⥤ BigAffineFppf B S hS :=
  liftedWeakIdealDownFunctor (A := A) ⋙ P.diagram

private theorem thickening_respectsIso :
    MorphismProperty.RespectsIso
      (@Stacks.Thickenings.IsThickening : MorphismProperty Scheme.{u}) := by
  apply MorphismProperty.RespectsIso.mk
  · intro X Y Z e f hf
    have hc : IsClosedImmersion (e.hom ≫ f) := by
      have : IsClosedImmersion e.hom := inferInstance
      have : IsClosedImmersion f := hf.1
      infer_instance
    have hs : Surjective (e.hom ≫ f) := by
      have : Surjective e.hom := inferInstance
      have : Surjective f := ⟨hf.2⟩
      infer_instance
    exact ⟨hc, hs.surj⟩
  · intro X Y Z e f hf
    have hc : IsClosedImmersion (f ≫ e.hom) := by
      have : IsClosedImmersion f := hf.1
      have : IsClosedImmersion e.hom := inferInstance
      infer_instance
    have hs : Surjective (f ≫ e.hom) := by
      have : Surjective f := ⟨hf.2⟩
      have : Surjective e.hom := inferInstance
      infer_instance
    exact ⟨hc, hs.surj⟩

omit [IsTopologicalRing A] [IsLinearTopology A A] in
/-- Every transition map of the quotient presentation of the formal space, viewed as a morphism
of schemes, is a thickening. -/
theorem quotientPresentation_transition_isThickening
    (i j : WeakIdeals A) (f : i ⟶ j) :
    Stacks.Thickenings.IsThickening
      ((BigAffineFppf.toScheme B S hS).map (P.diagram.map f)) := by
  let q := Spec.map (CommRingCat.ofHom
    (Ideal.Quotient.factor (show j.1 ≤ i.1 from leOfHom f)))
  let g := (BigAffineFppf.toScheme B S hS).map (P.diagram.map f)
  have hq : Stacks.Thickenings.IsThickening q :=
    quotient_factor_isThickening (show j.1 ≤ i.1 from leOfHom f) i.2 j.2
  have hArrow : Arrow.mk g ≅ Arrow.mk q :=
    Arrow.isoMk (P.quotientIso i) (P.quotientIso j)
      (P.quotientIso_natural f).symm
  exact (MorphismProperty.arrow_mk_iso_iff
    (@Stacks.Thickenings.IsThickening : MorphismProperty Scheme.{u}) hArrow).mpr hq

omit [IsTopologicalRing A] [IsLinearTopology A A] in
private theorem liftedQuotientDiagram_transitions_areThickenings
    {i j : LiftedWeakIdealIndex (A := A)} (f : i ⟶ j) :
    Stacks.Thickenings.IsThickening
      ((BigAffineFppf.toScheme B S hS).map
        ((liftedQuotientDiagram B S hS A X P).map f)) := by
  show Stacks.Thickenings.IsThickening
    ((BigAffineFppf.toScheme B S hS).map
      (P.diagram.map ((liftedWeakIdealDownFunctor (A := A)).map f)))
  exact quotientPresentation_transition_isThickening B S hS A X P
    i.down j.down ((liftedWeakIdealDownFunctor (A := A)).map f)

universe v w w₁ w₂

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (A : Type u) [CommRing A] [TopologicalSpace A]
  [IsTopologicalRing A] [IsLinearTopology A A]
  (X : FppfSheaf B S hS)
  (P : WeakIdealColimitPresentation B S hS A X)

/-- A morphism of big fppf objects that is a closed immersion of schemes becomes a monomorphism
after sheafified Yoneda. -/
private theorem mono_sheafifiedYoneda_map_of_isClosedImmersion
    {U V : BigFppfOver B S hS} (g : U ⟶ V)
    (hg : IsClosedImmersion ((BigFppfOver.toScheme B S hS).map g)) :
    Mono ((Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map g) := by
  have := hg
  exact Sheaf.mono_sheafifiedYoneda_map_of_mono_underlying _ (BigFppfOver.toScheme B S hS) g
    inferInstance

private theorem factor_from_compact_scheme
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (I : Type (u + 1)) [Preorder I] [Small.{u + 1} I]
    [Nonempty I] [IsDirected I (· ≤ ·)]
    (D : I ⥤ BigAffineFppf B S hS)
    (hD : ∀ ⦃i j : I⦄ (g : i ⟶ j),
      IsClosedImmersion ((BigAffineFppf.toScheme B S hS).map (D.map g)))
    (X : Sheaf (BigFppfOver.topology B S hS) (Type (u + 1)))
    (e : X ≅ colimit (D ⋙ BigAffineFppf.inclusion B S hS ⋙
      Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)))
    (U : BigFppfOver B S hS)
    [CompactSpace ((BigFppfOver.toScheme B S hS).obj U)]
    (f : (Sheaf.sheafifiedYoneda
      (BigFppfOver.topology B S hS)).obj U ⟶ X) :
    ∃ i : I, ∃ g : (Sheaf.sheafifiedYoneda
      (BigFppfOver.topology B S hS)).obj U ⟶
      (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj
        ((BigAffineFppf.inclusion B S hS).obj (D.obj i)),
      g ≫ colimit.ι (D ⋙ BigAffineFppf.inclusion B S hS ⋙
        Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)) i ≫ e.inv = f := by
  classical
  let J := BigFppfOver.topology B S hS
  let q := BigFppfOver.toScheme B S hS
  let F := Sheaf.sheafifiedYoneda J
  let G := D ⋙ BigAffineFppf.inclusion B S hS ⋙ F
  have htrans : ∀ i j (g : i ⟶ j), Mono (G.map g) := by
    intro i j g
    exact mono_sheafifiedYoneda_map_of_isClosedImmersion B S hS _ (hD g)
  let H := (sheafSections J (Type (u + 1))).obj (op U)
  have hUqc : J.IsQuasiCompactObject U :=
    isQuasiCompactObject_over_of_compact_scheme B S hS U
  have hbij : Function.Bijective (colimit.post G H) :=
    (Sheaf.injective_and_bijective_colimit_post_sheafSections J G U).2.2.1 hUqc htrans
  let α := f ≫ e.hom
  let s := (Sheaf.sectionEquiv J) α
  obtain ⟨z, hz⟩ := hbij.2 s
  let Gsec := G ⋙ H
  obtain ⟨i, x, hx⟩ := Concrete.isColimit_exists_rep Gsec (colimit.isColimit Gsec) z
  let gi : F.obj U ⟶ G.obj i := (Sheaf.sectionEquiv J).symm x
  have hpost (x : (G.obj i).obj.obj (op U)) :
      colimit.post G H (colimit.ι Gsec i x) = (colimit.ι G i).hom.app (op U) x :=
    ConcreteCategory.congr_hom (colimit.ι_post G H i) x
  have hgi : gi ≫ colimit.ι G i = α := by
    apply (Sheaf.sectionEquiv J).injective
    calc
      (Sheaf.sectionEquiv J) (gi ≫ colimit.ι G i) = (colimit.ι G i).hom.app (op U) x := by
        rw [Sheaf.sectionEquiv_comp]
        show (colimit.ι G i).hom.app (op U)
          ((Sheaf.sectionEquiv J) ((Sheaf.sectionEquiv J).symm x)) = _
        exact congrArg ((colimit.ι G i).hom.app (op U))
          ((Sheaf.sectionEquiv J).apply_symm_apply x)
      _ = colimit.post G H (colimit.ι Gsec i x) := (hpost x).symm
      _ = colimit.post G H z := congrArg (colimit.post G H) hx
      _ = s := hz
      _ = (Sheaf.sectionEquiv J) α := rfl
  refine ⟨i, gi, ?_⟩
  apply (cancel_mono e.hom).1
  calc
    (gi ≫ colimit.ι G i ≫ e.inv) ≫ e.hom = gi ≫ colimit.ι G i := by simp [Category.assoc]
    _ = f ≫ e.hom := hgi

private theorem quotientColimitInjection_mono
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (A : Type u) [CommRing A] [TopologicalSpace A]
    [IsTopologicalRing A] [IsLinearTopology A A]
    (X : Sheaf (BigFppfOver.topology B S hS) (Type (u + 1)))
    (P : WeakIdealColimitPresentation B S hS A X)
    [Nonempty (WeakIdeals A)]
    [IsDirected (WeakIdeals A) (· ≤ ·)]
    (J : WeakIdeals A) :
    Mono (colimit.ι (P.diagram ⋙ BigAffineFppf.inclusion B S hS ⋙
      Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)) J) := by
  apply Sheaf.mono_colimit_ι_of_mono_transition
  intro K L f
  exact mono_sheafifiedYoneda_map_of_isClosedImmersion B S hS _
    (quotientPresentation_transition_isThickening B S hS A X P K L f).1

private theorem weakIdeal_le_of_colimit_stage_map
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (A : Type u) [CommRing A] [TopologicalSpace A]
    [IsTopologicalRing A] [IsLinearTopology A A]
    (X : Sheaf (BigFppfOver.topology B S hS) (Type (u + 1)))
    (P : WeakIdealColimitPresentation B S hS A X)
    [Nonempty (WeakIdeals A)]
    [IsDirected (WeakIdeals A) (· ≤ ·)]
    {J K : WeakIdeals A} (g : P.diagram.obj J ⟶ P.diagram.obj K)
    (hcol : (Sheaf.sheafifiedYoneda
        (BigFppfOver.topology B S hS)).map
          ((BigAffineFppf.inclusion B S hS).map g) ≫
        colimit.ι (P.diagram ⋙ BigAffineFppf.inclusion B S hS ⋙
          Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)) K =
        colimit.ι (P.diagram ⋙ BigAffineFppf.inclusion B S hS ⋙
          Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)) J) :
    J ≤ K := by
  classical
  let T := BigAffineFppf.inclusion B S hS
  let F := Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)
  let GP := P.diagram ⋙ T ⋙ F
  have : (BigFppfOver.topology B S hS).Subcanonical :=
    bigFppfOver_subcanonical B S hS
  have : F.Faithful := Sheaf.sheafifiedYoneda_faithful (BigFppfOver.topology B S hS)
  obtain ⟨L, hJL, hKL⟩ := (inferInstance : IsDirected (WeakIdeals A) (· ≤ ·)).directed J K
  let tJL := P.diagram.map (homOfLE hJL)
  let tKL := P.diagram.map (homOfLE hKL)
  have hcolL : F.map (T.map (g ≫ tKL)) ≫ colimit.ι GP L =
      F.map (T.map tJL) ≫ colimit.ι GP L := by
    have hwKL := colimit.w (F := GP) (homOfLE hKL)
    have hwJL := colimit.w (F := GP) (homOfLE hJL)
    change F.map (T.map tKL) ≫ colimit.ι GP L = _ at hwKL
    change F.map (T.map tJL) ≫ colimit.ι GP L = _ at hwJL
    calc
      F.map (T.map (g ≫ tKL)) ≫ colimit.ι GP L =
          F.map (T.map g) ≫ colimit.ι GP K := by
            simp only [Functor.map_comp, Category.assoc]
            rw [hwKL]
      _ = colimit.ι GP J := hcol
      _ = F.map (T.map tJL) ≫ colimit.ι GP L := hwJL.symm
  have : Mono (colimit.ι GP L) := quotientColimitInjection_mono
    B S hS A X P L
  have hmap : F.map (T.map (g ≫ tKL)) = F.map (T.map tJL) :=
    (cancel_mono (colimit.ι GP L)).1 hcolL
  have hcat : g ≫ tKL = tJL :=
    (Functor.map_injective (F := T)) ((Functor.map_injective (F := F)) hmap)
  let qJ := P.quotientIso J
  let qK := P.quotientIso K
  let qL := P.quotientIso L
  let toSch := BigAffineFppf.toScheme B S hS
  let fKL : A ⧸ L.1 →+* A ⧸ K.1 :=
    Ideal.Quotient.factor (show L.1 ≤ K.1 from leOfHom (homOfLE hKL))
  let fJL : A ⧸ L.1 →+* A ⧸ J.1 :=
    Ideal.Quotient.factor (show L.1 ≤ J.1 from leOfHom (homOfLE hJL))
  let coord : Spec (.of (A ⧸ J.1)) ⟶ Spec (.of (A ⧸ K.1)) :=
    qJ.inv ≫ toSch.map g ≫ qK.hom
  let coordOp := Spec.fullyFaithful.preimage coord
  have hcoord : coordOp ≫ (CommRingCat.ofHom fKL).op =
      (CommRingCat.ofHom fJL).op := by
    apply Scheme.Spec.map_injective
    have hnKL := P.quotientIso_natural (homOfLE hKL)
    have hnJL := P.quotientIso_natural (homOfLE hJL)
    calc
      Scheme.Spec.map (coordOp ≫ (CommRingCat.ofHom fKL).op) =
          coord ≫ Scheme.Spec.map (CommRingCat.ofHom fKL).op := by simp [coord, coordOp]
      _ = qJ.inv ≫ toSch.map (g ≫ tKL) ≫ qL.hom := by
            dsimp [coord]
            rw [Functor.map_comp]
            simp only [Category.assoc]
            rw [hnKL]
      _ = qJ.inv ≫ toSch.map tJL ≫ qL.hom := by rw [hcat]
      _ = Scheme.Spec.map (CommRingCat.ofHom fJL).op := by
            dsimp [tJL, fJL]
            rw [hnJL]
            simp
  have hcoordRing : coordOp.unop.hom.comp fKL = fJL := by
    have h := congrArg Quiver.Hom.unop hcoord
    simp only [unop_comp, Quiver.Hom.unop_op] at h
    have h' := congrArg CommRingCat.Hom.hom h
    simpa using h'
  show K.1 ≤ J.1
  intro x hx
  have hval := congrArg
    (fun ψ : A ⧸ L.1 →+* A ⧸ J.1 => ψ (Ideal.Quotient.mk L.1 x)) hcoordRing
  change coordOp.unop.hom (fKL (Ideal.Quotient.mk L.1 x)) =
    fJL (Ideal.Quotient.mk L.1 x) at hval
  have hleft : fKL (Ideal.Quotient.mk L.1 x) = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr hx
  rw [hleft, map_zero] at hval
  have hright : fJL (Ideal.Quotient.mk L.1 x) = Ideal.Quotient.mk J.1 x := by
    simp [fJL, Ideal.Quotient.factor_mk]
  rw [hright] at hval
  exact Ideal.Quotient.eq_zero_iff_mem.mp hval.symm

private theorem compactSpace_of_thickening_source
    (hA : TopologicalRing.IsWeaklyAdmissible A)
    (P : WeakIdealColimitPresentation B S hS A X)
    (T : BigFppfOver B S hS)
    (f : (Sheaf.sheafifiedYoneda
      (BigFppfOver.topology B S hS)).obj T ⟶ X)
    (hf_thick : (MorphismProperty.relative
      (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS))
      (MorphismProperty.inverseImage
        (@Stacks.Thickenings.IsThickening : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS))) f) :
    CompactSpace ((BigFppfOver.toScheme B S hS).obj T) := by
  have : Nonempty (WeakIdeals A) := TopologicalRing.nonempty_weakIdealOfDefinitionIndex hA.1
  have : IsDirected (WeakIdeals A) (· ≤ ·) :=
    TopologicalRing.isDirected_weakIdealOfDefinitionIndex A
  have : Nonempty (LiftedWeakIdealIndex (A := A)) := liftedWeakIdeals_nonempty A hA
  have : IsDirected (LiftedWeakIdealIndex (A := A)) (· ≤ ·) := liftedWeakIdeals_directed A
  let Taff := BigAffineFppf.inclusion B S hS
  let F := Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)
  let D : LiftedWeakIdealIndex (A := A) ⥤ BigAffineFppf B S hS :=
    liftedWeakIdealDownFunctor (A := A) ⋙ P.diagram
  have hD : ∀ ⦃i j : LiftedWeakIdealIndex (A := A)⦄ (g : i ⟶ j),
      Stacks.Thickenings.IsThickening
        ((BigAffineFppf.toScheme B S hS).map (D.map g)) :=
    fun _ _ g => liftedQuotientDiagram_transitions_areThickenings B S hS A X P g
  let eFinal := Functor.Final.colimitIso (liftedWeakIdealDownFunctor (A := A))
    (P.diagram ⋙ Taff ⋙ F)
  let e : colimit (D ⋙ Taff ⋙ F) ≅ X := eFinal ≪≫ P.colimitIso.symm
  let i := ULift.up (Classical.choice (TopologicalRing.nonempty_weakIdealOfDefinitionIndex hA.1))
  let q := colimit.ι (D ⋙ Taff ⋙ F) i ≫ e.hom
  have hq := isThickening_colimitι B S hS D hD X e i
  have : (BigFppfOver.topology B S hS).Subcanonical :=
    bigFppfOver_subcanonical B S hS
  have : F.Full := Sheaf.sheafifiedYoneda_full (BigFppfOver.topology B S hS)
  let hb := hq.1.pullback f
  have hpull := hq.1.isPullback f
  have hpbT : Stacks.Thickenings.IsThickening
      ((BigFppfOver.toScheme B S hS).map (hq.1.snd f)) :=
    hq.2 f (hq.1.fst f) (hq.1.snd f) hpull
  let fst' : hb ⟶ (BigAffineFppf.inclusion B S hS).obj (D.obj i) :=
    F.preimage (hq.1.fst f)
  have hpbStage : Stacks.Thickenings.IsThickening
      ((BigFppfOver.toScheme B S hS).map fst') := by
    have hm : F.map fst' = hq.1.fst f := F.map_preimage _
    have hpull' : IsPullback (F.map (hq.1.snd f)) (F.map fst') f q := by
      rw [hm]
      exact hpull.flip
    exact hf_thick.2 q (F.map (hq.1.snd f)) fst' hpull'
  have : IsAffine
      ((BigAffineFppf.toScheme B S hS).obj (D.obj i)) :=
    (D.obj i).property
  have : CompactSpace
      ((BigFppfOver.toScheme B S hS).obj
        ((BigAffineFppf.inclusion B S hS).obj (D.obj i))) := by
    show CompactSpace ((BigAffineFppf.toScheme B S hS).obj (D.obj i))
    infer_instance
  have : CompactSpace
      ((BigFppfOver.toScheme B S hS).obj hb) :=
    hpbStage.1.isClosedEmbedding.compactSpace
  exact hpbT.2.compactSpace ((BigFppfOver.toScheme B S hS).map (hq.1.snd f)).continuous

/-- The map from a quotient stage of the canonical presentation to the formal space. -/
public noncomputable abbrev quotientMap (J : WeakIdeals A) :
    (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj
      ((BigAffineFppf.inclusion B S hS).obj (P.diagram.obj J)) ⟶ X :=
  colimit.ι
      (P.diagram ⋙ BigAffineFppf.inclusion B S hS ⋙
        Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)) J ≫
    P.colimitIso.inv

/-- The map from each quotient stage to the formal space is a monomorphism. -/
private theorem mono_quotientMap [Nonempty (WeakIdeals A)]
    [IsDirected (WeakIdeals A) (· ≤ ·)] (J : WeakIdeals A) :
    Mono (quotientMap B S hS A X P J) := by
  have := quotientColimitInjection_mono B S hS A X P J
  exact mono_comp _ _

/-- The stage map of the lifted diagram, followed by the identification of its colimit with the
formal space, is `quotientMap`. -/
private theorem colimit_ι_lifted_comp_hom
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (A : Type u) [CommRing A] [TopologicalSpace A]
    (X : FppfSheaf B S hS)
    (P : WeakIdealColimitPresentation B S hS A X) (J : WeakIdeals A) :
    colimit.ι (liftedWeakIdealDownFunctor (A := A) ⋙ P.diagram ⋙
        BigAffineFppf.inclusion B S hS ⋙
        Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)) (ULift.up J) ≫
      (Functor.Final.colimitIso (liftedWeakIdealDownFunctor (A := A))
        (P.diagram ⋙ BigAffineFppf.inclusion B S hS ⋙
          Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)) ≪≫
        P.colimitIso.symm).hom = quotientMap B S hS A X P J := by
  rw [Iso.trans_hom, ← Category.assoc]
  rw [Functor.Final.ι_colimitIso_hom]
  rfl

/-- Every weak ideal of definition gives a thickening of the formal space. -/
@[stacks 0AIC "thickening_classification"]
public theorem isThickening_quotient
    (hA : TopologicalRing.IsWeaklyAdmissible A)
    (J : WeakIdeals A) :
    (MorphismProperty.relative
      (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS))
      (MorphismProperty.inverseImage
        (@Stacks.Thickenings.IsThickening : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS)))
      (quotientMap B S hS A X P J) := by
  have : Nonempty (WeakIdeals A) := TopologicalRing.nonempty_weakIdealOfDefinitionIndex hA.1
  have : IsDirected (WeakIdeals A) (· ≤ ·) :=
    TopologicalRing.isDirected_weakIdealOfDefinitionIndex A
  have : Nonempty (LiftedWeakIdealIndex (A := A)) := liftedWeakIdeals_nonempty A hA
  have : IsDirected (LiftedWeakIdealIndex (A := A)) (· ≤ ·) := liftedWeakIdeals_directed A
  let T := BigAffineFppf.inclusion B S hS
  let F := Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)
  let G := P.diagram ⋙ T ⋙ F
  let D : LiftedWeakIdealIndex (A := A) ⥤ BigAffineFppf B S hS :=
    liftedWeakIdealDownFunctor (A := A) ⋙ P.diagram
  have hD : ∀ ⦃i j : LiftedWeakIdealIndex (A := A)⦄ (f : i ⟶ j),
      Stacks.Thickenings.IsThickening
        ((BigAffineFppf.toScheme B S hS).map (D.map f)) :=
    fun _ _ f => liftedQuotientDiagram_transitions_areThickenings B S hS A X P f
  let eFinal := Functor.Final.colimitIso (liftedWeakIdealDownFunctor (A := A)) G
  let e : colimit (D ⋙ T ⋙ F) ≅ X := eFinal ≪≫ P.colimitIso.symm
  have h := isThickening_colimitι B S hS D hD X e (ULift.up J)
  exact colimit_ι_lifted_comp_hom B S hS A X P J ▸ h

/-- Every weak ideal of definition gives a representable morphism from its
quotient scheme to the formal space. -/
@[stacks 0AIC "thickening_classification"]
public theorem relativelyRepresentable_quotient
    (hA : TopologicalRing.IsWeaklyAdmissible A)
    (J : WeakIdeals A) :
    (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).relativelyRepresentable
      (quotientMap B S hS A X P J) := (isThickening_quotient B S hS A X P hA J).1

/-- Any representable thickening from a scheme into the formal space is,
uniquely up to its weak ideal, a quotient stage of the canonical presentation. -/
@[stacks 0AIC "thickening_classification"]
public theorem existsUnique_weakIdeal_quotient
    (hA : TopologicalRing.IsWeaklyAdmissible A)
    (T : BigFppfOver B S hS)
    (f : (Sheaf.sheafifiedYoneda
      (BigFppfOver.topology B S hS)).obj T ⟶ X)
    (_hf_repr : (Sheaf.sheafifiedYoneda
      (BigFppfOver.topology B S hS)).relativelyRepresentable f)
    (hf_thick : (MorphismProperty.relative
      (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS))
      (MorphismProperty.inverseImage
        (@Stacks.Thickenings.IsThickening : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS))) f) :
    ∃! J : WeakIdeals A,
      ∃ e : T ≅ (BigAffineFppf.inclusion B S hS).obj (P.diagram.obj J),
      (Sheaf.sheafifiedYoneda
          (BigFppfOver.topology B S hS)).map e.hom ≫
          quotientMap B S hS A X P J = f := by
  have : Nonempty (WeakIdeals A) := TopologicalRing.nonempty_weakIdealOfDefinitionIndex hA.1
  have : IsDirected (WeakIdeals A) (· ≤ ·) :=
    TopologicalRing.isDirected_weakIdealOfDefinitionIndex A
  have : Nonempty (LiftedWeakIdealIndex (A := A)) := liftedWeakIdeals_nonempty A hA
  have : IsDirected (LiftedWeakIdealIndex (A := A)) (· ≤ ·) := liftedWeakIdeals_directed A
  let Taff := BigAffineFppf.inclusion B S hS
  let F := Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)
  let GP := P.diagram ⋙ Taff ⋙ F
  let D : LiftedWeakIdealIndex (A := A) ⥤ BigAffineFppf B S hS :=
    liftedWeakIdealDownFunctor (A := A) ⋙ P.diagram
  have hDclosed : ∀ ⦃i j : LiftedWeakIdealIndex (A := A)⦄ (g : i ⟶ j),
      IsClosedImmersion ((BigAffineFppf.toScheme B S hS).map (D.map g)) :=
    fun _ _ g => (liftedQuotientDiagram_transitions_areThickenings B S hS A X P g).1
  let eFinal := Functor.Final.colimitIso (liftedWeakIdealDownFunctor (A := A)) GP
  let eColim : colimit (D ⋙ Taff ⋙ F) ≅ X := eFinal ≪≫ P.colimitIso.symm
  have := compactSpace_of_thickening_source B S hS A X hA P T f hf_thick
  obtain ⟨i, g', hg'⟩ := factor_from_compact_scheme B S hS
    (LiftedWeakIdealIndex (A := A)) D hDclosed X eColim.symm T f
  have : (BigFppfOver.topology B S hS).Subcanonical :=
    bigFppfOver_subcanonical B S hS
  have : F.Full := Sheaf.sheafifiedYoneda_full (BigFppfOver.topology B S hS)
  obtain ⟨a, ha⟩ := F.map_surjective g'
  let J := i.down
  change T ⟶ Taff.obj (P.diagram.obj J) at a
  have hstage : colimit.ι (D ⋙ Taff ⋙ F) i ≫ eColim.hom = quotientMap B S hS A X P J :=
    colimit_ι_lifted_comp_hom B S hS A X P J
  have hfac : F.map a ≫ quotientMap B S hS A X P J = f := by
    calc
      F.map a ≫ quotientMap B S hS A X P J = F.map a ≫
          colimit.ι (D ⋙ Taff ⋙ F) i ≫ eColim.hom := congrArg (F.map a ≫ ·) hstage.symm
      _ = g' ≫ colimit.ι (D ⋙ Taff ⋙ F) i ≫ eColim.hom :=
        congrArg (fun z => z ≫ colimit.ι (D ⋙ Taff ⋙ F) i ≫ eColim.hom) ha
      _ = f := hg'
  have := mono_quotientMap B S hS A X P J
  have hpull : IsPullback (𝟙 (F.obj T)) (F.map a) f (quotientMap B S hS A X P J) :=
    isPullback_id_of_factorization (F.map a) f (quotientMap B S hS A X P J) hfac.symm
  have haThick : Stacks.Thickenings.IsThickening
      ((BigFppfOver.toScheme B S hS).map a) :=
    hf_thick.2 (quotientMap B S hS A X P J) (𝟙 (F.obj T)) a hpull
  have : IsAffine
      ((BigFppfOver.toScheme B S hS).obj
        (Taff.obj (P.diagram.obj J))) := (P.diagram.obj J).property
  have : IsClosedImmersion ((BigFppfOver.toScheme B S hS).map a) := haThick.1
  have hTaff : IsAffine ((BigFppfOver.toScheme B S hS).obj T) :=
    (IsClosedImmersion.isAffine_surjective_of_isAffine
      ((BigFppfOver.toScheme B S hS).map a)).1
  let V : BigAffineFppf B S hS := ⟨T, hTaff⟩
  let aOver : Taff.obj V ⟶ Taff.obj (P.diagram.obj J) := by
    simpa [V, Taff] using a
  let aBig : V ⟶ P.diagram.obj J := Taff.preimage aOver
  have haBig : Taff.map aBig = aOver := Taff.map_preimage aOver
  have haBigThick : Stacks.Thickenings.IsThickening
      ((BigAffineFppf.toScheme B S hS).map aBig) := by
    show Stacks.Thickenings.IsThickening
      ((BigFppfOver.toScheme B S hS).map (Taff.map aBig))
    rw [haBig]
    simpa [aOver, Taff] using haThick
  obtain ⟨K, hKJ, eSch, heSch⟩ := exists_weakIdeal_over_thickening_stage
    B S hS A X P J aBig haBigThick
  have heBase : eSch.hom ≫ B.inclusion.map (Taff.obj (P.diagram.obj K)).hom =
      B.inclusion.map (Taff.obj V).hom := by
    calc
      eSch.hom ≫ B.inclusion.map (Taff.obj (P.diagram.obj K)).hom =
          eSch.hom ≫ (B.inclusion.map (Taff.map (P.diagram.map (homOfLE hKJ))).left ≫
            B.inclusion.map (Taff.obj (P.diagram.obj J)).hom) := by
              rw [← Functor.map_comp, Over.w]
      _ = (eSch.hom ≫ B.inclusion.map
            (Taff.map (P.diagram.map (homOfLE hKJ))).left) ≫
            B.inclusion.map (Taff.obj (P.diagram.obj J)).hom := by simp [Category.assoc]
      _ = B.inclusion.map
            ((Taff.map aBig).left) ≫ B.inclusion.map (Taff.obj (P.diagram.obj J)).hom :=
              congrArg
                (fun z => z ≫ B.inclusion.map (Taff.obj (P.diagram.obj J)).hom) heSch.symm
      _ = B.inclusion.map (Taff.obj V).hom := by
            rw [← B.inclusion.map_comp, Over.w]
  let eBig := bigAffineIso_of_schemeIso_over B S hS V (P.diagram.obj K)
    eSch heBase
  let e : T ≅ Taff.obj (P.diagram.obj K) := Taff.mapIso eBig
  have heBig : (BigAffineFppf.toScheme B S hS).map eBig.hom = eSch.hom := by
    show B.inclusion.map
      ((Taff.map (Taff.preimage (Over.homMk (B.inclusion.preimage eSch.hom) _))).left) = _
    rw [Taff.map_preimage]
    exact B.inclusion.map_preimage eSch.hom
  have haBigEq : aBig = eBig.hom ≫ P.diagram.map (homOfLE hKJ) := by
    apply (Functor.map_injective (F := BigAffineFppf.toScheme B S hS))
    rw [Functor.map_comp, heBig]
    exact heSch
  have hmap : a = e.hom ≫ Taff.map (P.diagram.map (homOfLE hKJ)) := by
    calc
      a = aOver := rfl
      _ = Taff.map aBig := haBig.symm
      _ = Taff.map (eBig.hom ≫ P.diagram.map (homOfLE hKJ)) := congrArg Taff.map haBigEq
      _ = e.hom ≫ Taff.map (P.diagram.map (homOfLE hKJ)) := by
            simp [e, Functor.map_comp]
  have he : F.map e.hom ≫ quotientMap B S hS A X P K = f := by
    calc
      F.map e.hom ≫ quotientMap B S hS A X P K =
          F.map a ≫ quotientMap B S hS A X P J := by
            have hw : F.map (Taff.map (P.diagram.map (homOfLE hKJ))) ≫
                quotientMap B S hS A X P J = quotientMap B S hS A X P K := by
              show GP.map (homOfLE hKJ) ≫
                (colimit.ι GP J ≫ P.colimitIso.inv) = colimit.ι GP K ≫ P.colimitIso.inv
              rw [← Category.assoc, colimit.w]
            rw [hmap, F.map_comp, Category.assoc, hw]
      _ = f := hfac
  have key : ∀ (K K' : WeakIdeals A) (e : T ≅ Taff.obj (P.diagram.obj K))
      (e' : T ≅ Taff.obj (P.diagram.obj K')),
      F.map e.hom ≫ quotientMap B S hS A X P K = f →
      F.map e'.hom ≫ quotientMap B S hS A X P K' = f → K ≤ K' := by
    intro K K' e e' he he'
    let eStage : Taff.obj (P.diagram.obj K) ≅ Taff.obj (P.diagram.obj K') :=
      e.symm ≪≫ e'
    let g : P.diagram.obj K ⟶ P.diagram.obj K' := Taff.preimage eStage.hom
    have hg : Taff.map g = eStage.hom := Taff.map_preimage eStage.hom
    have hqeq : F.map (Taff.map g) ≫ quotientMap B S hS A X P K' =
        quotientMap B S hS A X P K := by
      calc
        F.map (Taff.map g) ≫ quotientMap B S hS A X P K' =
            F.map e.inv ≫ F.map e'.hom ≫ quotientMap B S hS A X P K' := by
              rw [hg]
              simp [eStage, Functor.map_comp, Category.assoc]
        _ = F.map e.inv ≫ (F.map e.hom ≫ quotientMap B S hS A X P K) := by rw [he, he']
        _ = quotientMap B S hS A X P K := by simp
    have hcol : F.map (Taff.map g) ≫ colimit.ι GP K' = colimit.ι GP K := by
      apply (cancel_mono P.colimitIso.inv).1
      rw [Category.assoc]
      exact hqeq
    exact weakIdeal_le_of_colimit_stage_map B S hS A X P g hcol
  refine ⟨K, ⟨e, he⟩, ?_⟩
  rintro K' ⟨e', he'⟩
  exact le_antisymm (key K' K e' e he' he) (key K K' e e' he he')

/-- The homomorphism from the presenting ring to the global sections of a
quotient stage, transported along a scheme isomorphism. -/
public noncomputable def sectionHomOfQuotientIso
    (J : WeakIdeals A)
    (T : BigFppfOver B S hS)
    (e : T ≅ (BigAffineFppf.inclusion B S hS).obj (P.diagram.obj J)) :
    A →+* Γ((BigFppfOver.toScheme B S hS).obj T, ⊤) :=
  ((CommRingCat.ofHom (Ideal.Quotient.mk J.1)) ≫
    (Scheme.ΓSpecIso (.of (A ⧸ J.1))).inv ≫
    Scheme.Γ.map (((BigFppfOver.toScheme B S hS).mapIso e ≪≫
      P.quotientIso J).hom.op)).hom

/-- The homomorphism on global sections induced by a representable thickening
into the formal space. The uniqueness and compatibility statements below show
that this construction does not depend on the chosen quotient description. -/
@[stacks 0AIC "thickening_classification"]
public noncomputable def inducedSectionHom
    (hA : TopologicalRing.IsWeaklyAdmissible A)
    (T : BigFppfOver B S hS)
    (f : (Sheaf.sheafifiedYoneda
      (BigFppfOver.topology B S hS)).obj T ⟶ X)
    (hf_repr : (Sheaf.sheafifiedYoneda
      (BigFppfOver.topology B S hS)).relativelyRepresentable f)
    (hf_thick : (MorphismProperty.relative
      (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS))
      (MorphismProperty.inverseImage
        (@Stacks.Thickenings.IsThickening : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS))) f) :
    A →+* Γ((BigFppfOver.toScheme B S hS).obj T, ⊤) :=
  let h := (existsUnique_weakIdeal_quotient B S hS A X P hA T f hf_repr hf_thick).exists
  let J := Classical.choose h
  let e := Classical.choose (Classical.choose_spec h)
  sectionHomOfQuotientIso B S hS A X P J T e

/-- At every quotient description compatible with the morphism to the formal
space, the induced map on sections is the canonical quotient map followed by
the affine global-sections isomorphism and transport to `T`. -/
@[stacks 0AIC "thickening_classification"]
public theorem inducedSectionHom_quotient
    (hA : TopologicalRing.IsWeaklyAdmissible A)
    (T : BigFppfOver B S hS)
    (f : (Sheaf.sheafifiedYoneda
      (BigFppfOver.topology B S hS)).obj T ⟶ X)
    (hf_repr : (Sheaf.sheafifiedYoneda
      (BigFppfOver.topology B S hS)).relativelyRepresentable f)
    (hf_thick : (MorphismProperty.relative
      (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS))
      (MorphismProperty.inverseImage
        (@Stacks.Thickenings.IsThickening : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS))) f)
    (J : WeakIdeals A)
    (e : T ≅ (BigAffineFppf.inclusion B S hS).obj (P.diagram.obj J))
    (he : (Sheaf.sheafifiedYoneda
      (BigFppfOver.topology B S hS)).map e.hom ≫
        quotientMap B S hS A X P J = f) :
    inducedSectionHom B S hS A X P hA T f hf_repr hf_thick =
      sectionHomOfQuotientIso B S hS A X P J T e := by
  let F := Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)
  let hU := existsUnique_weakIdeal_quotient B S hS A X P hA T f hf_repr hf_thick
  let h := hU.exists
  let J₀ := Classical.choose h
  have hJ₀ := Classical.choose_spec h
  have hJ : J₀ = J := hU.unique hJ₀ ⟨e, he⟩
  let e₀ := Classical.choose hJ₀
  have he₀ := Classical.choose_spec hJ₀
  show sectionHomOfQuotientIso B S hS A X P J₀ T e₀ = _
  subst J
  have : Nonempty (WeakIdeals A) := TopologicalRing.nonempty_weakIdealOfDefinitionIndex hA.1
  have : IsDirected (WeakIdeals A) (· ≤ ·) :=
    TopologicalRing.isDirected_weakIdealOfDefinitionIndex A
  have : (BigFppfOver.topology B S hS).Subcanonical :=
    bigFppfOver_subcanonical B S hS
  have : F.Faithful := Sheaf.sheafifiedYoneda_faithful (BigFppfOver.topology B S hS)
  have := mono_quotientMap B S hS A X P J₀
  have heIso : e₀ = e :=
    Iso.ext (F.map_injective ((cancel_mono (quotientMap B S hS A X P J₀)).1 (he₀.trans he.symm)))
  rw [heIso]

/-- The classifying ideal of a representable thickening is the kernel of the
homomorphism from the associated ring to its global sections. -/
@[stacks 0AIC "thickening_classification"]
public theorem quotient_ker_sections
    (hA : TopologicalRing.IsWeaklyAdmissible A)
    (T : BigFppfOver B S hS)
    (f : (Sheaf.sheafifiedYoneda
      (BigFppfOver.topology B S hS)).obj T ⟶ X)
    (hf_repr : (Sheaf.sheafifiedYoneda
      (BigFppfOver.topology B S hS)).relativelyRepresentable f)
    (hf_thick : (MorphismProperty.relative
      (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS))
      (MorphismProperty.inverseImage
        (@Stacks.Thickenings.IsThickening : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS))) f)
    (J : WeakIdeals A)
    (e : T ≅ (BigAffineFppf.inclusion B S hS).obj (P.diagram.obj J))
    (he : (Sheaf.sheafifiedYoneda
      (BigFppfOver.topology B S hS)).map e.hom ≫
        quotientMap B S hS A X P J = f) :
    RingHom.ker (inducedSectionHom B S hS A X P hA T f hf_repr hf_thick) = J.1 := by
  rw [inducedSectionHom_quotient B S hS A X P hA T f hf_repr hf_thick J e he]
  let g₁ := Scheme.ΓSpecIso (.of (A ⧸ J.1))
  let d := (BigFppfOver.toScheme B S hS).mapIso e ≪≫ P.quotientIso J
  let g₂ := Scheme.Γ.mapIso d.op
  let ψ : A ⧸ J.1 →+* Γ((BigFppfOver.toScheme B S hS).obj T, ⊤) :=
    g₂.hom.hom.comp g₁.inv.hom
  have hψ : Function.Injective ψ := g₂.commRingCatIsoToRingEquiv.injective.comp
    g₁.commRingCatIsoToRingEquiv.symm.injective
  show RingHom.ker (ψ.comp (Ideal.Quotient.mk J.1)) = J.1
  rw [RingHom.ker_comp_of_injective _ hψ, Ideal.mk_ker]

end AlgebraicGeometry.FormalSpace

end
