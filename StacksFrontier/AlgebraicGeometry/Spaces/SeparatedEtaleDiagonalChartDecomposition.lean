module

public import StacksFrontier.AlgebraicGeometry.Spaces.ComplexesWithSupport
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.ClosedImmersionFinitePresentation
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Unramified
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenCover
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparatedEtaleDiagonalPushforward
public import StacksFrontier.AlgebraicGeometry.Spaces.SheafSupport
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleAffineRefinement
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Etale
public import StacksFrontier.CategoryTheory.Sites.PairDisjointCover

/-!
# The diagonal of a separated étale morphism cuts every chart into two clopen pieces

Let `f : X ⟶ Y` be a separated étale morphism of algebraic spaces over a scheme `S` contained in a
big fppf site `B`, and let `Δ : X ⟶ X ×_Y X` be its relative diagonal. Then `Δ` is both an open
immersion and a closed immersion. Its base change along an étale chart `V ⟶ X ×_Y X` is a morphism
of schemes `V ×_{X ×_Y X} X ⟶ V` whose image is open and closed in the scheme underlying `V`; the
complement of that image is again an étale chart of `X ×_Y X`, and the two pieces form a covering
family of `V` by two disjoint monomorphisms:

`V = (V ×_{X ×_Y X} X) ⊔ V∖Δ`.

Consequently, for any sheaf on the small étale site of `X ×_Y X`, a section over `V` is exactly a
pair of sections over the two pieces.

## Main definitions

* `AlgebraicGeometry.Space.diagonalChart` and `AlgebraicGeometry.Space.diagonalChartHom`: the
  base-changed chart `V ×_{X ×_Y X} X`, read as an étale chart of `X ×_Y X` over `V`, and its
  structure morphism, whose underlying morphism of schemes is the cartesian projection.
* `AlgebraicGeometry.Space.diagonalChartComplement` and
  `AlgebraicGeometry.Space.diagonalChartComplementHom`: the complementary open subscheme of `V`,
  read as an étale chart of `X ×_Y X` over `V`, and its inclusion.

## Main results

* `AlgebraicGeometry.Space.isOpenImmersion_selfFibreDiagonal`: the relative diagonal of an étale
  morphism of algebraic spaces is an open immersion.
* `AlgebraicGeometry.Space.isClopen_diagonalChartRange`: the image of the cartesian projection
  `V ×_{X ×_Y X} X ⟶ V` is open and closed in the scheme underlying `V`.
* `AlgebraicGeometry.Space.mono_diagonalChartHom` and
  `AlgebraicGeometry.Space.mono_diagonalChartComplementHom`: both pieces include into `V` by
  monomorphisms.
* `AlgebraicGeometry.Space.ofArrows_diagonalChartPair_mem_topology`: the two pieces generate a
  covering sieve of `V`.
* `AlgebraicGeometry.Space.bot_mem_topology_of_diagonalChartPair`: an étale chart mapping to both
  pieces over `V` is covered by the empty sieve.
* `AlgebraicGeometry.Space.existsUnique_section_of_diagonalChartPair`: for a sheaf of types on the
  small étale site of `X ×_Y X`, a section over `V` is a pair of sections over the two pieces.

## References

* [Stacks Project, Tag 0HAP](https://stacks.math.columbia.edu/tag/0HAP)
* [Stacks Project, Tag 03HL](https://stacks.math.columbia.edu/tag/03HL)
* [Stacks Project, Tag 05W1](https://stacks.math.columbia.edu/tag/05W1)
* [Stacks Project, Tag 06CR](https://stacks.math.columbia.edu/tag/06CR)
* [Stacks Project, Tag 03EC](https://stacks.math.columbia.edu/tag/03EC)
-/

@[expose] public section

open CategoryTheory Opposite

universe w u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Monomorphisms of the small étale site -/

/-- A morphism of the small étale site of a presheaf whose underlying morphism of the big fppf site
is a monomorphism is a monomorphism. -/
theorem SmallEtale.mono_of_mono_toOver_map {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {U V : SmallEtale B S hS F} {k : U ⟶ V}
    (h : Mono ((SmallEtale.toOver B S hS F).map k)) : Mono k := by
  refine ⟨fun {T} g g' hgg' ↦ ObjectProperty.hom_ext _ (CostructuredArrow.hom_ext _ _ ?_)⟩
  exact (cancel_mono ((SmallEtale.toOver B S hS F).map k)).mp
    (congrArg (fun m : T ⟶ V ↦ (SmallEtale.toOver B S hS F).map m) hgg')

variable {X Y : AlgebraicSpaces B S hS}

/-! ### The diagonal of a separated étale morphism is a clopen immersion -/

/-- The relative diagonal of an étale morphism of algebraic spaces is an open immersion. -/
theorem isOpenImmersion_selfFibreDiagonal (f : X ⟶ Y) (het : IsEtale B S hS f.hom) :
    IsOpenImmersion B S hS (selfFibreDiagonal B S hS f).hom :=
  isOpenImmersion_diagonal_of_isUnramified B S hS X.property Y.property f.hom
    (isUnramified_of_isEtale B S hS het)

/-- The cartesian projection `V ×_{X ×_Y X} X ⟶ V` of the diagonal at an étale chart `V` of
`X ×_Y X`, as a morphism of the big fppf site. -/
noncomputable abbrev diagonalChartProj (f : X ⟶ Y) (hsep : IsSeparated B S hS f.hom)
    (V : SmallEtale B S hS (selfFibreSquare B S hS f).1) :
    (relativelyRepresentable_selfFibreDiagonal B S hS f hsep).pullback V.1.hom ⟶ V.1.left :=
  (relativelyRepresentable_selfFibreDiagonal B S hS f hsep).snd V.1.hom

/-- For a separated morphism, the cartesian projection of the diagonal at a chart is a closed
immersion of schemes. -/
theorem isClosedImmersion_diagonalChartProj (f : X ⟶ Y) (hsep : IsSeparated B S hS f.hom)
    (V : SmallEtale B S hS (selfFibreSquare B S hS f).1) :
    _root_.AlgebraicGeometry.IsClosedImmersion
      ((BigFppfOver.toScheme B S hS).map (diagonalChartProj B S hS f hsep V)) :=
  hsep.property_snd V.1.hom

/-- For an étale morphism, the cartesian projection of the diagonal at a chart is an open immersion
of schemes. -/
theorem isOpenImmersion_diagonalChartProj (f : X ⟶ Y) (het : IsEtale B S hS f.hom)
    (hsep : IsSeparated B S hS f.hom)
    (V : SmallEtale B S hS (selfFibreSquare B S hS f).1) :
    _root_.AlgebraicGeometry.IsOpenImmersion
      ((BigFppfOver.toScheme B S hS).map (diagonalChartProj B S hS f hsep V)) :=
  (isOpenImmersion_selfFibreDiagonal B S hS f het).property_snd V.1.hom

/-- The image of the cartesian projection of the diagonal in the scheme underlying a chart. -/
noncomputable abbrev diagonalChartRange (f : X ⟶ Y) (hsep : IsSeparated B S hS f.hom)
    (V : SmallEtale B S hS (selfFibreSquare B S hS f).1) : Set (chartScheme V) :=
  Set.range ((BigFppfOver.toScheme B S hS).map (diagonalChartProj B S hS f hsep V))

/-- The image of the diagonal in a chart is open and closed. -/
theorem isClopen_diagonalChartRange (f : X ⟶ Y) (het : IsEtale B S hS f.hom)
    (hsep : IsSeparated B S hS f.hom)
    (V : SmallEtale B S hS (selfFibreSquare B S hS f).1) :
    IsClopen (diagonalChartRange B S hS f hsep V) := by
  have := isClosedImmersion_diagonalChartProj B S hS f hsep V
  have := isOpenImmersion_diagonalChartProj B S hS f het hsep V
  exact ⟨((BigFppfOver.toScheme B S hS).map
      (diagonalChartProj B S hS f hsep V)).isClosedEmbedding.isClosed_range,
    ((BigFppfOver.toScheme B S hS).map
      (diagonalChartProj B S hS f hsep V)).isOpenEmbedding.isOpen_range⟩

/-! ### The two pieces of a chart -/

/-- The base-changed chart `V ×_{X ×_Y X} X`, read as an étale chart of `X ×_Y X` over `V`: the
image under the postcomposition functor of the base change of `V` along the diagonal. -/
noncomputable abbrev diagonalChart (f : X ⟶ Y) (het : IsEtale B S hS f.hom)
    (hsep : IsSeparated B S hS f.hom)
    (V : SmallEtale B S hS (selfFibreSquare B S hS f).1) :
    SmallEtale B S hS (selfFibreSquare B S hS f).1 :=
  (smallEtalePostcomp B S hS (selfFibreDiagonal B S hS f)
      (isEtale_selfFibreDiagonal B S hS f het)).obj
    ((smallBaseChange B S hS (selfFibreDiagonal B S hS f)
      (relativelyRepresentable_selfFibreDiagonal B S hS f hsep)).obj V)

/-- The structure morphism of `AlgebraicGeometry.Space.diagonalChart` over `V`: the counit of the
adjunction between postcomposition and base change of charts. -/
noncomputable abbrev diagonalChartHom (f : X ⟶ Y) (het : IsEtale B S hS f.hom)
    (hsep : IsSeparated B S hS f.hom)
    (V : SmallEtale B S hS (selfFibreSquare B S hS f).1) :
    diagonalChart B S hS f het hsep V ⟶ V :=
  (smallEtalePostcompBaseChangeAdjunction B S hS (selfFibreDiagonal B S hS f)
    (isEtale_selfFibreDiagonal B S hS f het)
    (relativelyRepresentable_selfFibreDiagonal B S hS f hsep)).counit.app V

/-- The underlying morphism of the big fppf site of `AlgebraicGeometry.Space.diagonalChartHom` is
the cartesian projection. -/
theorem toOver_map_diagonalChartHom (f : X ⟶ Y) (het : IsEtale B S hS f.hom)
    (hsep : IsSeparated B S hS f.hom)
    (V : SmallEtale B S hS (selfFibreSquare B S hS f).1) :
    (SmallEtale.toOver B S hS (selfFibreSquare B S hS f).1).map
        (diagonalChartHom B S hS f het hsep V) =
      diagonalChartProj B S hS f hsep V :=
  smallEtalePostcompBaseChangeAdjunction_counit_left B S hS (selfFibreDiagonal B S hS f)
    (isEtale_selfFibreDiagonal B S hS f het)
    (relativelyRepresentable_selfFibreDiagonal B S hS f hsep) V

/-- The complement of the image of the diagonal, as an open subscheme of the scheme underlying a
chart. -/
noncomputable def diagonalChartComplementOpens (f : X ⟶ Y) (het : IsEtale B S hS f.hom)
    (hsep : IsSeparated B S hS f.hom)
    (V : SmallEtale B S hS (selfFibreSquare B S hS f).1) : (chartScheme V).Opens :=
  ⟨(diagonalChartRange B S hS f hsep V)ᶜ,
    (isClopen_diagonalChartRange B S hS f het hsep V).1.isOpen_compl⟩

/-- The complement of the image of the diagonal in a chart, an open subscheme of the scheme
underlying `V`, read as an étale chart of `X ×_Y X` over `V`. -/
noncomputable def diagonalChartComplement (f : X ⟶ Y) (het : IsEtale B S hS f.hom)
    (hsep : IsSeparated B S hS f.hom)
    (V : SmallEtale B S hS (selfFibreSquare B S hS f).1) :
    SmallEtale B S hS (selfFibreSquare B S hS f).1 :=
  openChart B S hS (selfFibreSquare B S hS f).1 V
    (diagonalChartComplementOpens B S hS f het hsep V)

/-- The inclusion of `AlgebraicGeometry.Space.diagonalChartComplement` into `V`. -/
noncomputable def diagonalChartComplementHom (f : X ⟶ Y) (het : IsEtale B S hS f.hom)
    (hsep : IsSeparated B S hS f.hom)
    (V : SmallEtale B S hS (selfFibreSquare B S hS f).1) :
    diagonalChartComplement B S hS f het hsep V ⟶ V :=
  openChartInclusion B S hS (selfFibreSquare B S hS f).1 V
    (diagonalChartComplementOpens B S hS f het hsep V)

/-- The underlying morphism of schemes of the inclusion of the complement is the inclusion of the
open subscheme. -/
theorem toScheme_toOver_map_diagonalChartComplementHom (f : X ⟶ Y)
    (het : IsEtale B S hS f.hom) (hsep : IsSeparated B S hS f.hom)
    (V : SmallEtale B S hS (selfFibreSquare B S hS f).1) :
    (BigFppfOver.toScheme B S hS).map
        ((SmallEtale.toOver B S hS (selfFibreSquare B S hS f).1).map
          (diagonalChartComplementHom B S hS f het hsep V)) =
      (diagonalChartComplementOpens B S hS f het hsep V).ι :=
  toScheme_map_toOver_map_openChartInclusion B S hS (selfFibreSquare B S hS f).1 V _

/-- The image of the inclusion of the complementary chart is the complement of the image of the
diagonal. -/
theorem range_toScheme_toOver_map_diagonalChartComplementHom (f : X ⟶ Y)
    (het : IsEtale B S hS f.hom) (hsep : IsSeparated B S hS f.hom)
    (V : SmallEtale B S hS (selfFibreSquare B S hS f).1) :
    Set.range ((BigFppfOver.toScheme B S hS).map
        ((SmallEtale.toOver B S hS (selfFibreSquare B S hS f).1).map
          (diagonalChartComplementHom B S hS f het hsep V))) =
      (diagonalChartRange B S hS f hsep V)ᶜ := by
  rw [toScheme_toOver_map_diagonalChartComplementHom]
  exact (diagonalChartComplementOpens B S hS f het hsep V).range_ι

/-! ### The pair is a disjoint covering family -/

/-- The inclusion of the base-changed chart is a monomorphism. -/
theorem mono_diagonalChartHom (f : X ⟶ Y) (het : IsEtale B S hS f.hom)
    (hsep : IsSeparated B S hS f.hom)
    (V : SmallEtale B S hS (selfFibreSquare B S hS f).1) :
    Mono (diagonalChartHom B S hS f het hsep V) := by
  refine SmallEtale.mono_of_mono_toOver_map B S hS ?_
  rw [toOver_map_diagonalChartHom]
  exact inverseImage_isClosedImmersion_le_monomorphisms B S hS _
    (isClosedImmersion_diagonalChartProj B S hS f hsep V)

/-- The inclusion of the complementary chart is a monomorphism. -/
theorem mono_diagonalChartComplementHom (f : X ⟶ Y) (het : IsEtale B S hS f.hom)
    (hsep : IsSeparated B S hS f.hom)
    (V : SmallEtale B S hS (selfFibreSquare B S hS f).1) :
    Mono (diagonalChartComplementHom B S hS f het hsep V) := by
  refine SmallEtale.mono_of_mono_toOver_map B S hS
    (inverseImage_isOpenImmersion_le_monomorphisms _ ?_)
  change _root_.AlgebraicGeometry.IsOpenImmersion ((BigFppfOver.toScheme B S hS).map _)
  rw [toScheme_toOver_map_diagonalChartComplementHom]
  exact inferInstanceAs (_root_.AlgebraicGeometry.IsOpenImmersion
    (diagonalChartComplementOpens B S hS f het hsep V).ι)

/-- The image of the structure morphism of the base-changed chart is the image of the diagonal. -/
private theorem range_toScheme_toOver_map_diagonalChartHom (f : X ⟶ Y)
    (het : IsEtale B S hS f.hom) (hsep : IsSeparated B S hS f.hom)
    (V : SmallEtale B S hS (selfFibreSquare B S hS f).1) :
    Set.range ((BigFppfOver.toScheme B S hS).map
        ((SmallEtale.toOver B S hS (selfFibreSquare B S hS f).1).map
          (diagonalChartHom B S hS f het hsep V))) =
      diagonalChartRange B S hS f hsep V := by
  rw [toOver_map_diagonalChartHom]
  rfl

/-- The two pieces of a chart `V` generate a covering sieve of `V` in the small étale topology. -/
theorem ofArrows_diagonalChartPair_mem_topology (f : X ⟶ Y) (het : IsEtale B S hS f.hom)
    (hsep : IsSeparated B S hS f.hom)
    (V : SmallEtale B S hS (selfFibreSquare B S hS f).1) :
    Sieve.ofArrows
        (pairFamily (diagonalChart B S hS f het hsep V)
          (diagonalChartComplement B S hS f het hsep V))
        (pairHom (diagonalChartHom B S hS f het hsep V)
          (diagonalChartComplementHom B S hS f het hsep V)) ∈
      SmallEtale.topology B S hS (selfFibreSquare B S hS f).1 V := by
  refine SmallEtale.ofArrows_mem_topology B S hS (selfFibreSquare B S hS f).1 _ _ ?_
  rw [Scheme.ofArrows_mem_etalePrecoverage_iff]
  refine ⟨fun x ↦ ?_, fun i ↦ etale_toScheme_toOver_map B S hS
    (selfFibreSquare B S hS f).1 _⟩
  by_cases hx : x ∈ diagonalChartRange B S hS f hsep V
  · exact ⟨true, (range_toScheme_toOver_map_diagonalChartHom B S hS f het hsep V).ge hx⟩
  · refine ⟨false, ?_⟩
    change x ∈ Set.range ((BigFppfOver.toScheme B S hS).map
      ((SmallEtale.toOver B S hS (selfFibreSquare B S hS f).1).map
        (diagonalChartComplementHom B S hS f het hsep V)))
    rwa [range_toScheme_toOver_map_diagonalChartComplementHom]

/-- The two pieces of a chart `V` are disjoint: an étale chart mapping to both of them compatibly
over `V` is covered by the empty sieve. -/
theorem bot_mem_topology_of_diagonalChartPair (f : X ⟶ Y) (het : IsEtale B S hS f.hom)
    (hsep : IsSeparated B S hS f.hom)
    (V : SmallEtale B S hS (selfFibreSquare B S hS f).1)
    {Z : SmallEtale B S hS (selfFibreSquare B S hS f).1}
    (g : Z ⟶ diagonalChart B S hS f het hsep V)
    (g' : Z ⟶ diagonalChartComplement B S hS f het hsep V)
    (hg : g ≫ diagonalChartHom B S hS f het hsep V =
      g' ≫ diagonalChartComplementHom B S hS f het hsep V) :
    (⊥ : Sieve Z) ∈ SmallEtale.topology B S hS (selfFibreSquare B S hS f).1 Z := by
  refine SmallEtale.bot_mem_topology B S hS (selfFibreSquare B S hS f).1 Z ⟨fun z ↦ ?_⟩
  have hz := congrArg (fun k : Z ⟶ V ↦ ((BigFppfOver.toScheme B S hS).map
    ((SmallEtale.toOver B S hS (selfFibreSquare B S hS f).1).map k)) z) hg
  simp only [Functor.map_comp, Scheme.Hom.comp_apply] at hz
  have hmem := (range_toScheme_toOver_map_diagonalChartHom B S hS f het hsep V).le
    ⟨((BigFppfOver.toScheme B S hS).map
      ((SmallEtale.toOver B S hS (selfFibreSquare B S hS f).1).map g)) z, rfl⟩
  rw [hz] at hmem
  exact (range_toScheme_toOver_map_diagonalChartComplementHom B S hS f het hsep V).le
    ⟨_, rfl⟩ hmem

/-! ### Sections over a chart -/

/-- A section of a sheaf of types over an étale chart `V` of `X ×_Y X` is exactly a pair of
sections over the two clopen pieces the diagonal cuts `V` into. -/
theorem existsUnique_section_of_diagonalChartPair (f : X ⟶ Y) (het : IsEtale B S hS f.hom)
    (hsep : IsSeparated B S hS f.hom)
    {P : (SmallEtale B S hS (selfFibreSquare B S hS f).1)ᵒᵖ ⥤ Type w}
    (hP : Presieve.IsSheaf (SmallEtale.topology B S hS (selfFibreSquare B S hS f).1) P)
    (V : SmallEtale B S hS (selfFibreSquare B S hS f).1)
    (s : P.obj (op (diagonalChart B S hS f het hsep V)))
    (t : P.obj (op (diagonalChartComplement B S hS f het hsep V))) :
    ∃! x : P.obj (op V),
      P.map (diagonalChartHom B S hS f het hsep V).op x = s ∧
        P.map (diagonalChartComplementHom B S hS f het hsep V).op x = t :=
  hP.existsUnique_section_of_pair _ _
    (ofArrows_diagonalChartPair_mem_topology B S hS f het hsep V)
    (mono_diagonalChartHom B S hS f het hsep V)
    (mono_diagonalChartComplementHom B S hS f het hsep V)
    (bot_mem_topology_of_diagonalChartPair B S hS f het hsep V) s t

end AlgebraicGeometry.Space

end
