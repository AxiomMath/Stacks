module

public import Mathlib.CategoryTheory.Sites.Limits
public import Mathlib.CategoryTheory.Sites.LocallySurjective
public import StacksCore.CategoryTheory.Pullback
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.AtlasCovering
public import StacksFrontier.AlgebraicGeometry.Spaces.CoveringComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.SurjectiveOnPoints
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf.StandardCoverings

/-!
# Scheme refinements of the fppf coverings of algebraic spaces, and their surjectivity

Let `S` be a scheme contained in a big fppf site `B`. Every fppf covering of an algebraic
space over `S` is refined by an fppf covering whose members are schemes: each member of the
given family has a surjective étale scheme atlas, which is an fppf covering of it, and
composing the two coverings gives the refinement.

## Main results

* `AlgebraicGeometry.Space.exists_fppfCovering_scheme_refinement`: **Stacks 042T**.
* `AlgebraicGeometry.Space.isLocallySurjective_coproductDesc_of_isFppfCovering`:
  **Stacks 0469**, an fppf covering is jointly surjective as a map of fppf sheaves.
* `AlgebraicGeometry.Space.isLocallySurjective_of_surjective_flat_locallyOfFinitePresentation`
  is its one-member case: a single surjective, flat morphism which is locally of finite
  presentation is already surjective as a map of fppf sheaves.
* `AlgebraicGeometry.Space.reprSchemePointMap` and
  `AlgebraicGeometry.Space.residueFieldValuedPoint` identify the points of a representable
  presheaf with the points of the representing scheme, and
  `AlgebraicGeometry.Space.exists_preimage_of_jointlySurjective_yoneda` and
  `AlgebraicGeometry.Space.yoneda_fppfCovering_mem_fppfPrecoverage` transport an fppf covering
  by representables to an fppf covering of schemes.

## Implementation notes

A scheme over the base is represented by the Yoneda presheaf of an object of the chosen big
fppf site, and the refining family is indexed by the index type of the given family, so the
refinement morphisms and the new covering morphisms are produced together rather than through
an unnamed intermediate family. Composing the given covering with the one-member atlas
coverings of its sources indexes the composite by `Σ i, PUnit`, and
`AlgebraicGeometry.Space.IsFppfCovering.reindex` transports it back to the original index
type along the section `i ↦ ⟨i, PUnit.unit⟩`.

The surjectivity statement of Stacks 0469 is about the coproduct of the covering family taken
in the category of fppf sheaves of sets, so the coproduct and its descending map are given by
an arbitrary colimit cocone rather than by a chosen construction, and surjectivity is Mathlib's
`CategoryTheory.Sheaf.IsLocallySurjective`. Its proof pulls the family back along a
scheme-valued point of the target, refines the pullback by schemes using Stacks 042T, transports
that to an fppf covering of schemes, and refines it inside the site by Stacks 03WX; the
resulting covering sieve of the point witnesses local surjectivity.

## References

* [Stacks Project, Tag 042T](https://stacks.math.columbia.edu/tag/042T)
* [Stacks Project, Tag 0469](https://stacks.math.columbia.edu/tag/0469)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Space

universe u v

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Stacks 042T.** An fppf covering of an algebraic space over `S` admits a refinement by a
family of schemes which is again an fppf covering. -/
@[stacks 042T]
theorem exists_fppfCovering_scheme_refinement
    {I : Type v} {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (X : I → (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (f : ∀ i, X i ⟶ F)
    (hf : IsFppfCovering B S hS X f) :
    ∃ (T : I → BigFppfOver B S hS) (h : ∀ i, yoneda.obj (T i) ⟶ X i),
      IsFppfCovering B S hS (fun i => yoneda.obj (T i)) (fun i => h i ≫ f i) := by
  classical
  choose T h hsurj hetale using fun i => (hf.source_isAlgebraicSpace i).exists_atlas
  refine ⟨T, h, ?_⟩
  exact IsFppfCovering.reindex B S hS
    (isFppfCovering_comp B S hS I (fun _ => PUnit.{v + 1}) X
      (fun i _ => yoneda.obj (T i)) f (fun i _ => h i) hf
      (fun i => isFppfCovering_atlas B S hS (hf.source_isAlgebraicSpace i)
        (hsurj i) (hetale i)))
    (σ := fun i : I => (⟨i, PUnit.unit⟩ : Σ _ : I, PUnit.{v + 1}))
    (fun p => ⟨p.1, by cases p.2; rfl⟩)

/-! ### Points of a representable presheaf and points of the representing scheme -/

/-- The point of the representing scheme underlying a point of the presheaf of points of a
representable presheaf. -/
noncomputable def reprSchemePointMap (U : BigFppfOver B S hS) :
    points B S hS (yoneda.obj U) → ((BigFppfOver.toScheme B S hS).obj U) :=
  Quot.lift (fun p => (reprSchemePoint p).point)
    (fun _ _ h => reprSchemePoint_eq_of_commonExtension h)

/-- The point of the representing scheme attached to the class of a field-valued point is the
point underlying that field-valued point. -/
@[simp]
theorem reprSchemePointMap_class {U : BigFppfOver B S hS}
    (p : FieldValuedPoint B S hS (yoneda.obj U)) :
    reprSchemePointMap B S hS U (p.class B S hS (yoneda.obj U)) = (reprSchemePoint p).point :=
  rfl

/-- The field-valued point of a representable presheaf at a point of the representing scheme:
the spectrum of the residue field at that point, which lies in the site by
`AlgebraicGeometry.BigFppfSite.residueField_spec_contains`. -/
noncomputable def residueFieldValuedPoint (U : BigFppfOver B S hS)
    (x : (BigFppfOver.toScheme B S hS).obj U) : FieldValuedPoint B S hS (yoneda.obj U) :=
  have hSpec : B.Contains (Spec (.of (((BigFppfOver.toScheme B S hS).obj U).residueField x))) :=
    B.residueField_spec_contains
      (show B.Contains ((BigFppfOver.toScheme B S hS).obj U) from U.left.property) x
  let π : B.inclusion.obj (B.obj hSpec) ⟶
      B.inclusion.obj ((BigFppfOver.forget B S hS).obj U) :=
    ((BigFppfOver.toScheme B S hS).obj U).fromSpecResidueField x
  { carrier := ((BigFppfOver.toScheme B S hS).obj U).residueField x
    contained := hSpec
    toBase := π ≫ B.inclusion.map U.hom
    value := Over.homMk (B.inclusion.preimage π) (by
      ext
      change (B.inclusion.map (B.inclusion.preimage π)) ≫ B.inclusion.map U.hom =
        π ≫ B.inclusion.map U.hom
      rw [B.inclusion.map_preimage]) }

/-- The point of the representing scheme underlying
`AlgebraicGeometry.Space.residueFieldValuedPoint` is the point one started from. -/
@[simp]
theorem reprSchemePoint_residueFieldValuedPoint (U : BigFppfOver B S hS)
    (x : (BigFppfOver.toScheme B S hS).obj U) :
    (reprSchemePoint (residueFieldValuedPoint B S hS U x)).point = x := by
  simp only [reprSchemePoint, residueFieldValuedPoint, FieldValuedPoint.point]
  change (B.inclusion.map (B.inclusion.preimage _)).base _ = x
  rw [B.inclusion.map_preimage]
  exact Scheme.fromSpecResidueField_apply x _

/-- The identification of points is natural in the representing scheme. -/
theorem reprSchemePointMap_pointsMap {U V : BigFppfOver B S hS} (f : U ⟶ V)
    (x : points B S hS (yoneda.obj U)) :
    reprSchemePointMap B S hS V (pointsMap B S hS (yoneda.obj U) (yoneda.map f) x) =
      f.left.hom (reprSchemePointMap B S hS U x) := by
  refine Quot.inductionOn x fun p => ?_
  simp only [pointsMap_class, reprSchemePointMap_class]
  rfl

/-- A family of morphisms of the site whose Yoneda images are jointly surjective on the points
of the presheaves is jointly surjective on the points of the representing schemes. -/
theorem exists_preimage_of_jointlySurjective_yoneda
    {I : Type v} (U : I → BigFppfOver B S hS) (T : BigFppfOver B S hS) (f : ∀ i, U i ⟶ T)
    (h : (⋃ i, Set.range (pointsMap B S hS (yoneda.obj (U i)) (yoneda.map (f i)))) =
      Set.univ)
    (x : (BigFppfOver.toScheme B S hS).obj T) :
    ∃ i, ∃ y : (BigFppfOver.toScheme B S hS).obj (U i), (f i).left.hom y = x := by
  have hx : (residueFieldValuedPoint B S hS T x).class B S hS (yoneda.obj T) ∈
      ⋃ i, Set.range (pointsMap B S hS (yoneda.obj (U i)) (yoneda.map (f i))) := by
    rw [h]; exact Set.mem_univ _
  obtain ⟨i, p, hp⟩ := Set.mem_iUnion.mp hx
  refine ⟨i, reprSchemePointMap B S hS (U i) p, ?_⟩
  have hp' := congrArg (reprSchemePointMap B S hS T) hp
  rw [reprSchemePointMap_pointsMap, reprSchemePointMap_class,
    reprSchemePoint_residueFieldValuedPoint] at hp'
  exact hp'

/-- An fppf covering of algebraic spaces whose members are representable comes from an fppf
covering of the representing schemes. -/
theorem yoneda_fppfCovering_mem_fppfPrecoverage
    {I : Type v} (U : I → BigFppfOver B S hS) (T : BigFppfOver B S hS) (f : ∀ i, U i ⟶ T)
    (hf : IsFppfCovering B S hS (fun i => yoneda.obj (U i)) (fun i => yoneda.map (f i))) :
    (({ I₀ := I, X := fun i => U i, f := f } : PreZeroHypercover T).map
        (BigFppfOver.toScheme B S hS)).presieve₀ ∈
      Scheme.fppfPrecoverage ((BigFppfOver.toScheme B S hS).obj T) := by
  have hflat (i : I) : Flat ((BigFppfOver.toScheme B S hS).map (f i)) :=
    hf.flat i (U i) T (𝟙 _) (𝟙 _) (f i) (presheaf_etale_id B S hS (U i))
      (presheaf_etale_id B S hS T) (by simp)
  have hlfp (i : I) :
      LocallyOfFinitePresentation ((BigFppfOver.toScheme B S hS).map (f i)) :=
    hf.locallyOfFinitePresentation i (U i) T (𝟙 _) (𝟙 _) (f i)
      (presheaf_etale_id B S hS (U i)) (presheaf_etale_id B S hS T) (by simp)
  rw [Scheme.fppfPrecoverage, Scheme.presieve₀_mem_precoverage_iff]
  refine ⟨fun x => ?_, fun i => ⟨hflat i, hlfp i⟩⟩
  obtain ⟨i, y, hy⟩ := exists_preimage_of_jointlySurjective_yoneda B S hS U T f
    hf.jointly_surjective x
  exact ⟨i, y, hy⟩


/-! ### An fppf covering is surjective as a map of fppf sheaves -/

/-- **Stacks 0469.** The map from the coproduct of an fppf covering family of algebraic spaces
over `S`, taken in the category of fppf sheaves of sets, to its target is surjective as a map
of fppf sheaves. -/
@[stacks 0469]
theorem isLocallySurjective_coproductDesc_of_isFppfCovering
    {I : Type v} {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (X : I → (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (f : ∀ i, X i ⟶ F)
    (hf : IsFppfCovering B S hS X f)
    (G : Sheaf (BigFppfOver.topology B S hS) (Type u))
    (ι : ∀ i, (⟨X i, (hf.source_isAlgebraicSpace i).isSheaf⟩ :
      Sheaf (BigFppfOver.topology B S hS) (Type u)) ⟶ G)
    (hG : IsColimit (Cofan.mk G ι)) :
    Sheaf.IsLocallySurjective
      (hG.desc (Cofan.mk
        (⟨F, hf.target_isAlgebraicSpace.isSheaf⟩ :
          Sheaf (BigFppfOver.topology B S hS) (Type u))
        (fun i =>
          (Sheaf.homEquiv (X :=
            (⟨X i, (hf.source_isAlgebraicSpace i).isSheaf⟩ :
              Sheaf (BigFppfOver.topology B S hS) (Type u)))
            (Y :=
            (⟨F, hf.target_isAlgebraicSpace.isSheaf⟩ :
              Sheaf (BigFppfOver.topology B S hS) (Type u)))).symm (f i)))) := by
  classical
  let J := BigFppfOver.topology B S hS
  let Fsheaf : Sheaf J (Type u) := ⟨F, hf.target_isAlgebraicSpace.isSheaf⟩
  let Xsheaf (i : I) : Sheaf J (Type u) := ⟨X i, (hf.source_isAlgebraicSpace i).isSheaf⟩
  let fi (i : I) : Xsheaf i ⟶ Fsheaf :=
    (Sheaf.homEquiv (X := Xsheaf i) (Y := Fsheaf)).symm (f i)
  let d : G ⟶ Fsheaf := hG.desc (Cofan.mk Fsheaf fi)
  show Sheaf.IsLocallySurjective d
  show Presheaf.IsLocallySurjective J d.hom
  refine ⟨?_⟩
  intro U ξ
  let g : yoneda.obj U ⟶ F := yonedaEquiv.symm ξ
  let Fspace : AlgebraicSpaces B S hS := ⟨F, hf.target_isAlgebraicSpace⟩
  let Xspace (i : I) : AlgebraicSpaces B S hS := ⟨X i, hf.source_isAlgebraicSpace i⟩
  let gspace : (⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩ :
      AlgebraicSpaces B S hS) ⟶ Fspace := ObjectProperty.homMk g
  let fspace (i : I) : Xspace i ⟶ Fspace := ObjectProperty.homMk (f i)
  let Y (i : I) := AlgebraicSpaces.fiberProduct B S hS gspace (fspace i)
  have hY : IsFppfCovering B S hS (fun i => (Y i).1) (fun i => pullback.fst g (f i)) :=
    isFppfCovering_fibreProduct B S hS Xspace fspace gspace hf
  obtain ⟨T, a, hT⟩ := exists_fppfCovering_scheme_refinement B S hS
    (fun i => (Y i).1) (fun i => pullback.fst g (f i)) hY
  let p₁ (i : I) := pullback.fst gspace.hom (fspace i).hom
  let p₂ (i : I) := pullback.snd gspace.hom (fspace i).hom
  let aa (i : I) : yoneda.obj (T i) ⟶ pullback gspace.hom (fspace i).hom := by
    simpa [Y, AlgebraicSpaces.fiberProduct] using a i
  let q (i : I) : T i ⟶ U := yonedaEquiv (aa i ≫ p₁ i)
  have hproj : ∀ i, aa i ≫ p₁ i = yoneda.map (q i) := by
    intro i
    apply (yonedaEquiv (X := T i) (F := yoneda.obj U)).injective
    simp only [q, yonedaEquiv_yoneda_map]
  have hT' : IsFppfCovering B S hS (fun i => yoneda.obj (T i)) (fun i => yoneda.map (q i)) := by
    have heq : (fun i => yoneda.map (q i)) = (fun i => a i ≫ pullback.fst g (f i)) := by
      funext i
      calc
        yoneda.map (q i) = aa i ≫ p₁ i := (hproj i).symm
        _ = a i ≫ pullback.fst g (f i) := by
          show a i ≫ pullback.fst gspace.hom (fspace i).hom = _
          rfl
    rw [heq]
    exact hT
  let E : PreZeroHypercover U := ⟨I, T, q⟩
  let ES := (E.map (BigFppfOver.forget B S hS)).map B.inclusion
  have hE : ES.presieve₀ ∈ Scheme.fppfPrecoverage (B.inclusion.obj U.left) := by
    simpa [ES, E, PreZeroHypercover.map, BigFppfOver.toScheme] using
      yoneda_fppfCovering_mem_fppfPrecoverage B S hS T U q hT'
  obtain ⟨V, hV, hRef⟩ := exists_isCovering_refining_fppfCovering B U.left ES hE
  rcases hRef with ⟨ref⟩
  let Vover : PreZeroHypercover U :=
    { I₀ := V.I₀
      X j := Over.mk (V.f j ≫ U.hom)
      f j := Over.homMk (V.f j) }
  have hVbase : V.sieve₀ ∈ B.topology U.left := by
    show V.sieve₀ ∈ B.precoverage.toGrothendieck U.left
    rw [Precoverage.mem_toGrothendieck_iff]
    have hmem : V.presieve₀ ∈ B.precoverage.coverings U.left := ⟨V, rfl, hV⟩
    simpa [PreZeroHypercover.sieve₀] using Precoverage.Saturate.of U.left V.presieve₀ hmem
  have hVover : Vover.sieve₀ ∈ J U := by
    show Vover.sieve₀ ∈ B.topology.over (B.obj hS) U
    rw [GrothendieckTopology.mem_over_iff, Sieve.overEquiv_ofArrows]
    simpa [Vover, PreZeroHypercover.sieve₀] using hVbase
  apply J.superset_covering ?_ hVover
  intro W k hk
  obtain ⟨j, l, hl⟩ := Sieve.ofArrows.exists hk
  let j0 : V.I₀ := j
  let jmap : (PreZeroHypercover.map B.inclusion V).I₀ := j0
  let i : I := ref.s₀ jmap
  have hw : ref.h₀ jmap ≫ B.inclusion.map (q i).left = B.inclusion.map (V.f j0) := by
    simpa [ES, E, PreZeroHypercover.map, jmap, j0, i] using ref.w₀ jmap
  have hpre : B.inclusion.map (B.inclusion.preimage (ref.h₀ jmap)) = ref.h₀ jmap :=
    B.inclusion.map_preimage _
  have hqmap : B.inclusion.map (T i).hom =
      B.inclusion.map (q i).left ≫ B.inclusion.map U.hom := by
    rw [← (q i).w, Functor.map_comp]
  have hrbase : (B.inclusion.preimage (ref.h₀ jmap)) ≫ (T i).hom = (Vover.X j0).hom :=
    B.inclusion.map_injective <| (B.inclusion.map_comp _ _).trans
      ((congrArg (fun t => t ≫ B.inclusion.map (T i).hom) hpre).trans
      ((congrArg (fun t => ref.h₀ jmap ≫ t) hqmap).trans
      ((Category.assoc _ _ _).symm.trans
      ((congrArg (fun t => t ≫ B.inclusion.map U.hom) hw).trans
        ((B.inclusion.map_comp _ _).symm.trans (by simp [Vover]))))))
  let r : Vover.X j ⟶ T i := Over.homMk (B.inclusion.preimage (ref.h₀ jmap)) hrbase
  have hrfac : r ≫ q i = Vover.f j := by
    refine Over.OverMorphism.ext (B.inclusion.map_injective ?_)
    show B.inclusion.map
      (B.inclusion.preimage (ref.h₀ jmap) ≫ (q i).left) = B.inclusion.map (V.f j0)
    exact (B.inclusion.map_comp _ _).trans
      ((congrArg (fun t => t ≫ B.inclusion.map (q i).left) hpre).trans hw)
  have hcomp : (l ≫ r) ≫ q i = k := by rw [Category.assoc, hrfac, hl.symm]
  let η : yoneda.obj W ⟶ X i := yoneda.map (l ≫ r) ≫ aa i ≫ p₂ i
  have hη : η ≫ f i = yoneda.map k ≫ g := by
    show (yoneda.map (l ≫ r) ≫ aa i ≫ p₂ i) ≫ (fspace i).hom = yoneda.map k ≫ g
    have hpc : p₂ i ≫ (fspace i).hom = p₁ i ≫ g := by
      simpa [p₁, p₂, gspace] using (pullback.condition).symm
    simp only [Category.assoc, hpc]
    simp only [← Category.assoc, hproj, ← yoneda.map_comp, hcomp]
  let z := η.app (Opposite.op W) (𝟙 W)
  let y := (ι i).hom.app (Opposite.op W) z
  refine ⟨y, ?_⟩
  have hsection' : (f i).app (Opposite.op W) z = F.map k.op ξ := by
    have hsection := congrArg (yonedaEquiv (X := W) (F := F)) hη
    rw [yonedaEquiv_comp, show yonedaEquiv η = z from rfl] at hsection
    rw [yonedaEquiv_comp, yonedaEquiv_yoneda_map] at hsection
    simpa [g] using hsection
  have hdesc := hG.fac (Cofan.mk Fsheaf fi) ⟨i⟩
  have hdesc' := congrArg
    (fun m : Xsheaf i ⟶ Fsheaf => m.hom.app (Opposite.op W) z) hdesc
  show d.hom.app (Opposite.op W) y = _
  simpa [y] using hdesc'.trans hsection'

/-- A surjective, flat morphism of algebraic spaces over `S` which is locally of finite
presentation is surjective as a morphism of fppf sheaves: it is a one-member fppf covering of
its target, so `AlgebraicGeometry.Space.isLocallySurjective_coproductDesc_of_isFppfCovering`
applies to the constant family it forms. -/
theorem isLocallySurjective_of_surjective_flat_locallyOfFinitePresentation
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (f : X ⟶ Y) (hsurj : IsSurjective B S hS f) (hflat : IsFlat B S hS f)
    (hfp : IsLocallyOfFinitePresentation B S hS f) :
    Presheaf.IsLocallySurjective (BigFppfOver.topology B S hS) f := by
  let hcover : IsFppfCovering B S hS (fun _ : PUnit.{1} => X) (fun _ => f) :=
    { target_isAlgebraicSpace := hY
      source_isAlgebraicSpace := fun _ => hX
      flat := fun _ => hflat
      locallyOfFinitePresentation := fun _ => hfp
      jointly_surjective := by
        ext y
        simp only [Set.mem_iUnion, Set.mem_range, Set.mem_univ, iff_true]
        obtain ⟨x, hx⟩ := hsurj y
        exact ⟨PUnit.unit, x, hx⟩ }
  let Xsheaf : Sheaf (BigFppfOver.topology B S hS) (Type u) := ⟨X, hX.isSheaf⟩
  let Ysheaf : Sheaf (BigFppfOver.topology B S hS) (Type u) := ⟨Y, hY.isSheaf⟩
  let fsheaf : Xsheaf ⟶ Ysheaf := (Sheaf.homEquiv (X := Xsheaf) (Y := Ysheaf)).symm f
  have hcolim : IsColimit (Cofan.mk Xsheaf (fun _ : PUnit.{1} => 𝟙 Xsheaf)) :=
    Cofan.isColimitMkOfUnique (Iso.refl Xsheaf) PUnit.{1}
  have hloc := isLocallySurjective_coproductDesc_of_isFppfCovering B S hS
    (fun _ : PUnit.{1} => X) (fun _ => f) hcover Xsheaf (fun _ => 𝟙 Xsheaf) hcolim
  have hdesc : hcolim.desc (Cofan.mk Ysheaf (fun _ : PUnit.{1} => fsheaf)) = fsheaf := by
    refine hcolim.hom_ext fun i => ?_
    simpa using hcolim.fac (Cofan.mk Ysheaf (fun _ : PUnit.{1} => fsheaf)) i
  have hfsheaf : fsheaf.hom = f := by
    show Sheaf.homEquiv (X := Xsheaf) (Y := Ysheaf) fsheaf = f
    simp [fsheaf]
  change Presheaf.IsLocallySurjective (BigFppfOver.topology B S hS)
    (hcolim.desc (Cofan.mk Ysheaf (fun _ : PUnit.{1} => fsheaf))).hom at hloc
  simpa only [hdesc, hfsheaf] using hloc

end AlgebraicGeometry.Space

end
