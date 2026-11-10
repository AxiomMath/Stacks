module

public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf.FibreProducts
public import StacksCore.Tactic.StacksAttribute

/-!
# The big affine fppf site

Let `B` be a big fppf site containing a scheme `S`.  The standard fppf covering families on
affine schemes over `S` satisfy the site axioms: they contain the isomorphisms, they are
stable under composition, and they are stable under base change.

## Main results

* `AlgebraicGeometry.bigAffineFppf_isSite`: the standard fppf covering families of affine
  schemes over `S` form a site.

## Implementation notes

The assertion is stated for the family-valued covering predicate via
`CategoryTheory.IsSite`, so it retains the chosen standard coverings rather than only the
Grothendieck topology they generate.  The three site axioms are checked by transporting the
corresponding closure properties of `AlgebraicGeometry.Scheme.fppfPrecoverage` along the
canonical functor to schemes, using that a standard fppf covering is exactly an fppf
covering family which is finite, has affine source and target, and whose members are of
finite presentation.  Stability under base change additionally needs that the fibre product
of two objects of the site is again one, which is the closure of the size cutoff under
pullbacks.

## References

* [Stacks Project, Tag 021T](https://stacks.math.columbia.edu/tag/021T)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u v

namespace AlgebraicGeometry

/-- A standard fppf covering family is an fppf covering family. -/
private lemma mem_fppfPrecoverage_of_isStandardFppfCovering {T : Scheme.{u}} {I : Type v}
    {U : I → Scheme.{u}} {f : ∀ i, U i ⟶ T}
    (h : AlgebraicGeometry.IsStandardFppfCovering U f) :
    Presieve.ofArrows U f ∈ Scheme.fppfPrecoverage T := by
  rw [Scheme.fppfPrecoverage, Scheme.ofArrows_mem_precoverage_iff]
  constructor
  · intro x
    have hx : x ∈ ⋃ i, Set.range (f i) := by rw [h.jointly_surjective]; simp
    simpa only [Set.mem_iUnion, Set.mem_range] using hx
  · exact fun i => ⟨h.flat i, (h.finite_presentation i).1⟩

/-- A finite fppf covering family of an affine scheme by affine schemes whose members are
of finite presentation is a standard fppf covering family. -/
private lemma isStandardFppfCovering_of_mem_fppfPrecoverage {T : Scheme.{u}} {I : Type v}
    {U : I → Scheme.{u}} {f : ∀ i, U i ⟶ T}
    (hI : Finite I) (hT : IsAffine T) (hU : ∀ i, IsAffine (U i))
    (hFP : ∀ i, AlgebraicGeometry.FinitePresentation (f i))
    (h : Presieve.ofArrows U f ∈ Scheme.fppfPrecoverage T) :
    AlgebraicGeometry.IsStandardFppfCovering U f := by
  rw [Scheme.fppfPrecoverage, Scheme.ofArrows_mem_precoverage_iff] at h
  refine ⟨hI, hT, hU, fun i => (h.2 i).1, hFP, ?_⟩
  rw [Set.eq_univ_iff_forall]
  intro x
  obtain ⟨i, y, hy⟩ := h.1 x
  exact Set.mem_iUnion.mpr ⟨i, Set.mem_range.mpr ⟨y, hy⟩⟩

/-- A one-member family consisting of an isomorphism of affine schemes is a standard fppf
covering family. -/
private lemma isStandardFppfCovering_singleton {I : Type v} [Unique I]
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsAffine X] [IsAffine Y] [IsIso f] :
    AlgebraicGeometry.IsStandardFppfCovering (fun _ : I => X) (fun _ => f) := by
  let : Flat f := inferInstance
  let : LocallyOfFinitePresentation f := inferInstance
  let : Surjective f := inferInstance
  let : QuasiCompact f := inferInstance
  let : QuasiSeparated f := inferInstance
  refine ⟨inferInstance, inferInstance, (fun _ => inferInstance),
    (fun _ => inferInstance), (fun _ => ⟨inferInstance, inferInstance, inferInstance⟩), ?_⟩
  rw [Set.eq_univ_iff_forall]
  intro y
  obtain ⟨x, hx⟩ := f.surjective y
  exact Set.mem_iUnion.mpr ⟨default, Set.mem_range.mpr ⟨x, hx⟩⟩

/-- The singleton family of an isomorphism is an fppf covering family. -/
private lemma singleton_mem_fppfPrecoverage_of_isIso {X Y : Scheme.{u}} (f : X ⟶ Y) [IsIso f] :
    Presieve.singleton f ∈ Scheme.fppfPrecoverage Y := by
  let : Flat f := inferInstance
  let : LocallyOfFinitePresentation f := inferInstance
  let : Surjective f := inferInstance
  exact f.singleton_mem_fppfPrecoverage

/-- The image under `toScheme` of a standard fppf covering of the big affine fppf category is an
fppf covering family. -/
private lemma presieve₀_map_toScheme_mem_fppfPrecoverage {B : AlgebraicGeometry.BigFppfSite.{u}}
    {S : Scheme.{u}} {hS : B.Contains S} {X : AlgebraicGeometry.BigAffineFppf B S hS}
    {E : PreZeroHypercover.{u + 1} X}
    (h : AlgebraicGeometry.BigAffineFppf.IsStandardFppfCovering B S hS ⟨X, E⟩) :
    (E.map (AlgebraicGeometry.BigAffineFppf.toScheme B S hS)).presieve₀ ∈
      Scheme.fppfPrecoverage ((AlgebraicGeometry.BigAffineFppf.toScheme B S hS).obj X) := by
  apply mem_fppfPrecoverage_of_isStandardFppfCovering
  simpa [AlgebraicGeometry.BigAffineFppf.IsStandardFppfCovering, PreZeroHypercover.presieve₀,
    PreZeroHypercover.map] using h

/-- **Stacks 021T.** Standard fppf coverings of affine schemes over `S` satisfy the site
axioms. -/
@[stacks 021T]
public theorem bigAffineFppf_isSite (B : AlgebraicGeometry.BigFppfSite.{u})
    (S : Scheme.{u}) (hS : B.Contains S) :
    IsSite (AlgebraicGeometry.BigAffineFppf.IsCovering B S hS) := by
  let K : AlgebraicGeometry.BigAffineFppf B S hS ⥤ B.Schemes :=
    AlgebraicGeometry.BigAffineFppf.inclusion B S hS ⋙
      AlgebraicGeometry.BigFppfOver.forget B S hS
  let G : AlgebraicGeometry.BigAffineFppf B S hS ⥤ Scheme.{u} :=
    AlgebraicGeometry.BigAffineFppf.toScheme B S hS
  let : Scheme.fppfPrecoverage.HasIsos := ⟨by
    intro X Y f hf
    let : IsIso f := hf
    exact singleton_mem_fppfPrecoverage_of_isIso f⟩
  refine ⟨?_, ?_, ?_⟩
  · intro U V f hf
    change B.IsCovering ⟨K.obj U, (PreZeroHypercover.singleton f).map K⟩ ∧ _
    refine ⟨?_, ?_⟩
    · have heq : (PreZeroHypercover.singleton f).map K =
          PreZeroHypercover.singleton (K.map f) :=
        PreZeroHypercover.ext rfl HEq.rfl HEq.rfl
      rw [heq]
      exact B.isSite.1 (K.map f)
    · let : IsIso f := hf
      let : IsIso (G.map f) := Functor.map_isIso G f
      let : IsAffine (G.obj V) := V.property
      let : IsAffine (G.obj U) := U.property
      have hstd := isStandardFppfCovering_singleton
        (I := (PreZeroHypercover.singleton f).I₀) (G.map f)
      simpa [AlgebraicGeometry.BigAffineFppf.IsStandardFppfCovering, G,
        PreZeroHypercover.singleton, PreZeroHypercover.singleton_X,
        PreZeroHypercover.singleton_f] using hstd
  · intro E hE F hF h
    change B.IsCovering ⟨K.obj E.1, E.2.map K⟩ ∧
        AlgebraicGeometry.BigAffineFppf.IsStandardFppfCovering B S hS E at hE
    change (∀ i, B.IsCovering ⟨K.obj (F i).1, (F i).2.map K⟩ ∧
        AlgebraicGeometry.BigAffineFppf.IsStandardFppfCovering B S hS (F i)) at hF
    change B.IsCovering ⟨K.obj E.1,
        (E.2.bind fun i => (F i).2.pushforward (eqToHom (h i))).map K⟩ ∧ _
    have hstdE := hE.2
    have hQE : (E.2.map G).presieve₀ ∈ Scheme.fppfPrecoverage (G.obj E.1) :=
      presieve₀_map_toScheme_mem_fppfPrecoverage hstdE
    have hQF (i : E.2.I₀) : ((F i).2.map G).presieve₀ ∈
        Scheme.fppfPrecoverage (G.obj (F i).1) :=
      presieve₀_map_toScheme_mem_fppfPrecoverage (hF i).2
    have hcomp := B.isSite.2.1 ⟨K.obj E.1, E.2.map K⟩ hE.1
      (fun i => ⟨K.obj (F i).1, (F i).2.map K⟩) (fun i => (hF i).1)
      (fun i => congrArg K.obj (h i))
    have hQcomp := Scheme.fppfPrecoverage.comp_mem_coverings
      (fun i => G.map (E.2.f i))
      (by simpa [PreZeroHypercover.map] using hQE)
      (fun i j => G.map ((F i).2.f j) ≫ G.map (eqToHom (h i)))
      (fun i => by
        have hi := hQF i
        let Ei : Scheme.fppfPrecoverage.ZeroHypercover (G.obj (F i).1) :=
          ⟨(F i).2.map G, hi⟩
        have hiso : Presieve.singleton (G.map (eqToHom (h i))) ∈
            Scheme.fppfPrecoverage (G.obj (E.2.X i)) := by
          let : IsIso (G.map (eqToHom (h i))) :=
            Functor.map_isIso G (eqToHom (h i))
          exact singleton_mem_fppfPrecoverage_of_isIso _
        have hi' := (Ei.pushforward (G.map (eqToHom (h i))) hiso).mem₀
        simpa [Ei, PreZeroHypercover.presieve₀, PreZeroHypercover.pushforward,
          Precoverage.ZeroHypercover.pushforward, PreZeroHypercover.map] using hi')
    refine ⟨?_, ?_⟩
    · simpa [PreZeroHypercover.map, PreZeroHypercover.bind,
        PreZeroHypercover.pushforward, Functor.map_comp, eqToHom_map,
        Category.assoc] using hcomp
    · let : Finite E.2.I₀ := hstdE.finite_index
      let : ∀ i, Finite (F i).2.I₀ := fun i => (hF i).2.finite_index
      have hstd := isStandardFppfCovering_of_mem_fppfPrecoverage
        (T := G.obj E.1) (U := fun ij : Σ i, (F i).2.I₀ =>
          G.obj ((F ij.1).2.X ij.2))
        (f := fun ij => G.map ((F ij.1).2.f ij.2) ≫
          G.map (eqToHom (h ij.1)) ≫ G.map (E.2.f ij.1)) (by infer_instance)
        (by simpa [G] using hstdE.affine_target)
        (fun ij => by
          simpa [PreZeroHypercover.map, PreZeroHypercover.bind,
            PreZeroHypercover.pushforward, G] using (hF ij.1).2.affine_source ij.2)
        (fun ij => by
          have hf := hstdE.finite_presentation ij.1
          have hg := (hF ij.1).2.finite_presentation ij.2
          let : LocallyOfFinitePresentation
              (G.map (eqToHom (h ij.1))) := inferInstance
          let : QuasiCompact (G.map (eqToHom (h ij.1))) := inferInstance
          let : QuasiSeparated (G.map (eqToHom (h ij.1))) := inferInstance
          let : LocallyOfFinitePresentation (G.map ((F ij.1).2.f ij.2)) := hg.1
          let : LocallyOfFinitePresentation (G.map (E.2.f ij.1)) := hf.1
          let : QuasiCompact (G.map ((F ij.1).2.f ij.2)) := hg.2.1
          let : QuasiCompact (G.map (E.2.f ij.1)) := hf.2.1
          let : QuasiSeparated (G.map ((F ij.1).2.f ij.2)) := hg.2.2
          let : QuasiSeparated (G.map (E.2.f ij.1)) := hf.2.2
          exact ⟨inferInstance, inferInstance, inferInstance⟩)
        (by
          simpa [PreZeroHypercover.map, PreZeroHypercover.bind,
            PreZeroHypercover.pushforward, Functor.map_comp,
            PreZeroHypercover.presieve₀, G] using hQcomp)
      simpa [AlgebraicGeometry.BigAffineFppf.IsStandardFppfCovering,
        PreZeroHypercover.bind, PreZeroHypercover.pushforward, G] using hstd
  · intro E hE V g
    change B.IsCovering ⟨K.obj E.1, E.2.map K⟩ ∧
        AlgebraicGeometry.BigAffineFppf.IsStandardFppfCovering B S hS E at hE
    have hstdE := hE.2
    have hQE : (E.2.map G).presieve₀ ∈ Scheme.fppfPrecoverage (G.obj E.1) :=
      presieve₀_map_toScheme_mem_fppfPrecoverage hstdE
    obtain ⟨P, π₁, π₂, hpb, hcov⟩ := B.isSite.2.2
      ⟨K.obj E.1, E.2.map K⟩ hE.1 (K.obj V) (K.map g)
    have : PreservesLimitsOfShape WalkingCospan B.inclusion := inferInstance
    have hpbB (i : E.2.I₀) : IsPullback
        (B.inclusion.map (π₁ i)) (B.inclusion.map (π₂ i))
        (G.map (E.2.f i)) (G.map g) :=
      Functor.map_isPullback B.inclusion (hpb i)
    have hQbase := Scheme.fppfPrecoverage.mem_coverings_of_isPullback
      (fun i => G.map (E.2.f i))
      (by simpa [PreZeroHypercover.map] using hQE)
      (G.map g)
      (P := fun i => B.inclusion.obj (P i))
      (fun i => B.inclusion.map (π₂ i)) (fun i => B.inclusion.map (π₁ i))
      (fun i => (hpbB i).flip)
    change E.2.I₀ → B.Schemes at P
    change (i : E.2.I₀) → P i ⟶ K.obj (E.2.X i) at π₁
    change (i : E.2.I₀) → P i ⟶ K.obj V at π₂
    have hPaff (i : E.2.I₀) : IsAffine (B.inclusion.obj (P i)) := by
      let : IsAffine (G.obj V) := V.property
      let : IsAffine (G.obj (E.2.X i)) := (E.2.X i).property
      let : IsAffine (G.obj E.1) := E.1.property
      have hAffPB : IsAffine (pullback (G.map (E.2.f i)) (G.map g)) :=
        Scheme.Pullback.isAffine_of_isAffine_isAffine_isAffine _ _
      exact (IsAffine.iff_of_isIso (hpbB i).isoPullback.hom).mpr hAffPB
    let Qobj (i : E.2.I₀) : AlgebraicGeometry.BigAffineFppf B S hS :=
      ⟨Over.mk (π₂ i ≫ V.obj.hom), hPaff i⟩
    have heq (i : E.2.I₀) :
        π₁ i ≫ (E.2.f i).hom.left = π₂ i ≫ g.hom.left := (hpb i).w
    let p₁ (i : E.2.I₀) : Qobj i ⟶ E.2.X i :=
      ObjectProperty.homMk <| Over.homMk (π₁ i) (by
        calc
          π₁ i ≫ (E.2.X i).obj.hom =
              (π₁ i ≫ (E.2.f i).hom.left) ≫ E.1.obj.hom := by
                rw [← (E.2.f i).hom.w]
                exact (Category.assoc _ _ _).symm
          _ = (π₂ i ≫ g.hom.left) ≫ E.1.obj.hom := by rw [heq i]
          _ = π₂ i ≫ V.obj.hom := by rw [Category.assoc, g.hom.w])
    let p₂ (i : E.2.I₀) : Qobj i ⟶ V :=
      ObjectProperty.homMk <| Over.homMk (π₂ i) rfl
    have : ReflectsLimitsOfShape WalkingCospan
        (AlgebraicGeometry.BigAffineFppf.inclusion B S hS) := inferInstance
    have : ReflectsLimitsOfShape WalkingCospan
        (AlgebraicGeometry.BigFppfOver.forget B S hS) := inferInstance
    have : ReflectsLimitsOfShape WalkingCospan K := inferInstance
    refine ⟨Qobj, p₁, p₂, ?_, ?_⟩
    · intro i
      apply IsPullback.of_map_of_faithful K
      change IsPullback (π₁ i) (π₂ i) (K.map (E.2.f i)) (K.map g)
      exact hpb i
    · have hFPbase (i : E.2.I₀) : AlgebraicGeometry.FinitePresentation
          (B.inclusion.map (π₂ i)) :=
        ⟨MorphismProperty.IsStableUnderBaseChange.of_isPullback (hpbB i)
            (hstdE.finite_presentation i).1,
          MorphismProperty.IsStableUnderBaseChange.of_isPullback (hpbB i)
            (hstdE.finite_presentation i).2.1,
          MorphismProperty.IsStableUnderBaseChange.of_isPullback (hpbB i)
            (hstdE.finite_presentation i).2.2⟩
      have hstdP := isStandardFppfCovering_of_mem_fppfPrecoverage (T := G.obj V)
        hstdE.finite_index V.property hPaff hFPbase hQbase
      let E' : PreZeroHypercover V := ⟨E.2.I₀, Qobj, p₂⟩
      constructor
      · change B.IsCovering ⟨K.obj V, E'.map K⟩
        convert hcov using 1
        congr 1
      · simpa [AlgebraicGeometry.BigAffineFppf.IsStandardFppfCovering,
          PreZeroHypercover.map, G, Qobj, p₂] using hstdP

end AlgebraicGeometry
