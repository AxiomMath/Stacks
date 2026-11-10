module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.CoveringAlgebraic
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartRespectsIso
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.PointsOfFiniteType

/-!
# A nonempty algebraic space locally of finite type over an algebraically closed field has a
rational point

Let `k` be an algebraically closed field whose spectrum is the base of a big fppf site, and let
`X` be an algebraic space over it whose structural morphism is locally of finite type. If `X` has
a point then it has a *rational point*: a section over the base object of the site.

## Main results

* `AlgebraicGeometry.Space.nonempty_obj_base_of_nonempty_points`: the rational point.

## Implementation notes

The statement is the case `Y = Spec k` of **Stacks 0487**
(`AlgebraicGeometry.Space.isSurjective_iff_surjective_app_isAlgClosed`): a morphism of algebraic
spaces locally of finite type is surjective exactly when it is surjective on `k`-valued points
for every algebraically closed `k`. Taking for the morphism the structural one
`X ⟶ Spec k`, surjectivity holds because the target has at most one point — the underlying scheme
of the base object is the spectrum of a field — while the source has at least one by hypothesis;
and the resulting surjectivity on `k`-valued points produces a section over the object
`Spec k ⟶ Spec k` given by the inverse of the identification, which is isomorphic to the base
object of the site.

The structural morphism is taken into the *represented* terminal presheaf
`yoneda.obj (Over.mk (𝟙 (B.obj hS)))` rather than into `⊤_`, so that the surjectivity Stacks 0487
returns is surjectivity onto a set of morphisms of the site, whose elements are exhibited
directly.

## References

* [Stacks Project, Tag 0487](https://stacks.math.columbia.edu/tag/0487)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Space

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **A section over an object of the site with a nonempty underlying scheme gives a point.** The
field-valued point is the residue field at any point of that scheme, with the restriction of the
section along the canonical morphism. -/
theorem nonempty_points_of_section (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (T : BigFppfOver B S hS) (hT : Nonempty ((BigFppfOver.toScheme B S hS).obj T))
    (s : F.obj (op T)) :
    Nonempty (points B S hS F) := by
  obtain ⟨x⟩ := hT
  refine ⟨FieldValuedPoint.class B S hS F
    { carrier := (schemePointRepresentative B S hS T x).carrier
      contained := (schemePointRepresentative B S hS T x).contained
      toBase := (schemePointRepresentative B S hS T x).toBase
      value := F.map ((schemePointRepresentative B S hS T x).value :
        (schemePointRepresentative B S hS T x).siteObject B S hS (yoneda.obj T) ⟶ T).op s }⟩

/-- **A nonempty algebraic space locally of finite type over an algebraically closed field has a
rational point.** Let the base `S` of the big fppf site be identified with the spectrum of an
algebraically closed field `k`, and let `X` be an algebraic space over `S` whose structural
morphism is locally of finite type. If `X` has a point then it has a section over the base object
`Over.mk (𝟙 (B.obj hS))` of the site.

This is the case of a structural morphism of Stacks 0487: the morphism to the represented
terminal presheaf is surjective, because the target has a single point, so it is surjective on
`k`-valued points. -/
theorem nonempty_obj_base_of_nonempty_points
    (k : Type u) [Field k] [IsAlgClosed k] (e : S ≅ Spec (.of k))
    (X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hX : IsAlgebraicSpace B S hS X)
    (hlft : IsLocallyOfFiniteType B S hS (terminal.from X))
    (hne : Nonempty (points B S hS X)) :
    Nonempty (X.obj (op (Over.mk (𝟙 (B.obj hS))))) := by
  classical
  set T₀ : BigFppfOver B S hS := Over.mk (𝟙 (B.obj hS)) with hT₀
  have hterm : IsTerminal (yoneda.obj T₀ : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) :=
    isTerminal_yoneda_obj_base B S hS
  have hY : IsAlgebraicSpace B S hS (yoneda.obj T₀) := isAlgebraicSpace_yoneda B S hS T₀
  -- The structural morphism of `X`, into the represented terminal presheaf.
  set f : X ⟶ yoneda.obj T₀ := hterm.from X with hf
  have hflft : IsLocallyOfFiniteType B S hS f := by
    have _ := isLocallyOfFiniteType_respectsIso B S hS
    have hι : (⊤_ ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u)) ≅ yoneda.obj T₀ :=
      terminalIsTerminal.uniqueUpToIso hterm
    have hfeq : f = terminal.from X ≫ hι.hom := hterm.hom_ext _ _
    rw [hfeq]
    exact MorphismProperty.RespectsIso.postcomp _ hι.hom _ hlft
  -- The target has at most one point, so `f` is surjective on points.
  have hone : Subsingleton (Spec (CommRingCat.of k)) := by
    change Subsingleton (PrimeSpectrum k); infer_instance
  have _ : Subsingleton ((BigFppfOver.toScheme B S hS).obj T₀) :=
    ⟨fun x y ↦ e.hom.injective (hone.elim _ _)⟩
  have hsub : Subsingleton (points B S hS (yoneda.obj T₀)) :=
    (pointsEquivScheme B S hS T₀).subsingleton
  have hsurj : IsSurjective B S hS f := by
    intro y
    obtain ⟨x⟩ := hne
    exact ⟨x, hsub.elim _ _⟩
  -- Stacks 0487 at `k` itself, with the structure morphism the inverse identification.
  have hk : B.Contains (Spec (.of k)) := by
    change (Spec (CommRingCat.of k)).size < B.cutoff
    rw [← Scheme.size_congr e]
    exact hS
  have happ := (isSurjective_iff_surjective_app_isAlgClosed B S hS hX hY f hflft).mp hsurj
    k hk e.inv
  obtain ⟨s, -⟩ := happ (Over.mkIdTerminal.from _)
  -- The object `Spec k ⟶ S` of the site is isomorphic to the base object.
  set m : B.obj hk ⟶ B.obj hS := ⟨e.inv⟩ with hm
  have _ : IsIso (B.inclusion.map m) := by
    change IsIso e.inv; infer_instance
  have _ : IsIso m := isIso_of_fully_faithful B.inclusion m
  have ei : Over.mk m ≅ T₀ := Over.isoMk (asIso m) (Category.comp_id m)
  exact ⟨X.map ei.inv.op s⟩

end AlgebraicGeometry.Space

end
