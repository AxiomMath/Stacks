module

public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import StacksFrontier.Examples.GroupSchemes.XorGroup

/-!
# Group schemes covered by two sections of their structure morphism

Let `p : G ⟶ S` be a morphism of schemes admitting two sections `c₀, c₁ : S ⟶ G` which are open
immersions whose images cover `G`. Then `G` is two copies of `S` glued along the overlap of the
two sections, and it carries a group law over `S` for which `c₀` is the identity section and `c₁`
is a section of order two: on the chart indexed by `b`, multiplication adds labels in `ZMod 2`.

`Stacks.Examples.SectionCoverData` records such a `p` together with its two sections, and
`Stacks.Examples.SectionCoverData.xorGroupPresentation` turns it into the data of
`Stacks.Examples.XorGroupPresentation`, hence into a group object over `S`. Separately, the
structure morphism of such a `G` inherits from the identity every property that is Zariski local
at the source, and is quasi-compact as soon as `S` is compact and quasi-separated.

## Main definitions

* `Stacks.Examples.SectionCoverData`: a morphism of schemes together with two sections whose
  images form an open cover.
* `Stacks.Examples.SectionCoverData.xorGroupPresentation`: the induced presentation of the group
  law.
* `Stacks.Examples.SectionCoverData.grpObj`: the resulting group object over the base.

## Main results

* `Stacks.Examples.SectionCoverData.proj_prop`: the structure morphism satisfies every property
  that is Zariski local at the source and holds for identity morphisms.
* `Stacks.Examples.SectionCoverData.quasiCompact_proj`: the structure morphism is quasi-compact
  when the base is compact and quasi-separated.

## Implementation notes

The two charts are indexed by `Bool` rather than by `Fin 2`, so that multiplication of labels is
`xor` and the group axioms reduce to `Bool.xor_assoc` and its companions. Each piece of the
resulting presentation is the terminal object `Over.mk (𝟙 S)` of the slice category, which is
what makes every piecewise comparison of morphisms automatic.

The fibre square is covered by the four products of charts. The chart morphisms of
`Scheme.Pullback.openCoverOfLeftRight` are only definitionally the expected maps, so
`SectionCoverData.productChart` names the chart morphism and everything below is stated in terms
of it; likewise the underlying object of a tensor product in the slice category is only
definitionally a fibre product, so `Stacks.Examples.tensorLeftToPullback` names the comparison
morphism instead of relying on that identification.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open MonoidalCategory CartesianMonoidalCategory

universe u

namespace Stacks.Examples

/-- The unique morphism of a scheme over `S` to the terminal object `Over.mk (𝟙 S)`. -/
public noncomputable def overUnit {S : Scheme.{u}} (T : CategoryTheory.Over S) :
    T ⟶ Over.mk (𝟙 S) :=
  Over.homMk T.hom (Category.comp_id _)

/-- A morphism of schemes `proj : total ⟶ S` together with two sections that are open immersions
and whose images cover `total`. -/
public structure SectionCoverData (S : Scheme.{u}) where
  /-- The scheme over `S`. -/
  total : Scheme.{u}
  /-- The structure morphism. -/
  proj : total ⟶ S
  /-- The two sections, indexed by `Bool`. -/
  chart : Bool → (S ⟶ total)
  /-- Each chart is a section of the structure morphism. -/
  chart_comp_proj : ∀ b, chart b ≫ proj = 𝟙 S
  /-- Each chart is an open immersion. -/
  isOpenImmersion_chart : ∀ b, IsOpenImmersion (chart b)
  /-- The two charts cover the total space. -/
  exists_chart_eq : ∀ x : total, ∃ (b : Bool) (y : S), (chart b).base y = x

namespace SectionCoverData

variable {S : Scheme.{u}} (D : SectionCoverData S)

/-- The open cover of the total space by the two charts. -/
public noncomputable def cover : D.total.OpenCover :=
  Scheme.Cover.mkOfCovers Bool (fun _ => S) D.chart D.exists_chart_eq
    (fun b => D.isOpenImmersion_chart b)

/-- The chart of `D.cover` indexed by `b` is the section `D.chart b`. -/
public lemma cover_f (b : Bool) : D.cover.f b = D.chart b := rfl

/-- The total space of a section cover, as a scheme over `S`. -/
public noncomputable abbrev over : CategoryTheory.Over S := Over.mk D.proj

/-- The structure morphism of `D.over` is `D.proj`. -/
public lemma over_hom : D.over.hom = D.proj := rfl

/-- The open cover of the fibre square by the four products of charts. -/
public noncomputable abbrev productCover : (pullback D.proj D.proj).OpenCover :=
  Scheme.Pullback.openCoverOfLeftRight D.cover D.cover D.proj D.proj

/-- The chart of the fibre square indexed by a pair of labels. -/
public noncomputable def productChart (b c : Bool) :
    pullback (D.chart b ≫ D.proj) (D.chart c ≫ D.proj) ⟶ pullback D.proj D.proj :=
  pullback.map _ _ _ _ (D.chart b) (D.chart c) (𝟙 S)
    (Category.comp_id _) (Category.comp_id _)

/-- The first projection of the chart indexed by `(b, c)` is the section `D.chart b`. -/
public lemma productChart_comp_fst (b c : Bool) :
    D.productChart b c ≫ pullback.fst D.proj D.proj =
      pullback.fst (D.chart b ≫ D.proj) (D.chart c ≫ D.proj) ≫ D.chart b :=
  pullback.lift_fst _ _ _

/-- The second projection of the chart indexed by `(b, c)` is the section `D.chart c`. -/
public lemma productChart_comp_snd (b c : Bool) :
    D.productChart b c ≫ pullback.snd D.proj D.proj =
      pullback.snd (D.chart b ≫ D.proj) (D.chart c ≫ D.proj) ≫ D.chart c :=
  pullback.lift_snd _ _ _

/-- Two morphisms to the base are equal if they agree after composing with a section and the
structure morphism, because each section is a right inverse of the structure morphism. -/
private theorem eq_of_comp_chart_comp_proj {T : Scheme.{u}} {x y : T ⟶ S} {a c : Bool}
    (h : x ≫ D.chart a ≫ D.proj = y ≫ D.chart c ≫ D.proj) : x = y := by
  simpa only [D.chart_comp_proj, Category.comp_id] using h

/-- On the chart indexed by a pair of labels the two projections of the fibre square agree,
because both charts are sections. -/
public lemma pullback_fst_eq_snd (b c : Bool) :
    pullback.fst (D.chart b ≫ D.proj) (D.chart c ≫ D.proj) =
      pullback.snd (D.chart b ≫ D.proj) (D.chart c ≫ D.proj) :=
  D.eq_of_comp_chart_comp_proj pullback.condition

/-- The multiplication of the group law, read on the chart indexed by a pair of labels: project
to the first factor and land in the chart indexed by the `xor` of the labels. -/
public noncomputable def productChartMap (b c : Bool) :
    pullback (D.chart b ≫ D.proj) (D.chart c ≫ D.proj) ⟶ D.total :=
  pullback.fst (D.chart b ≫ D.proj) (D.chart c ≫ D.proj) ≫ D.chart (b ^^ c)

/-- Two morphisms to the base that agree after composing with two charts each also agree after
composing with the chart indexed by the `xor` of the labels. -/
public lemma chart_xor_compatible {T : Scheme.{u}} (x y : T ⟶ S) (a b c d : Bool)
    (h₁ : x ≫ D.chart a = y ≫ D.chart c) (h₂ : x ≫ D.chart b = y ≫ D.chart d) :
    x ≫ D.chart (a ^^ b) = y ≫ D.chart (c ^^ d) := by
  have hxy : x = y :=
    D.eq_of_comp_chart_comp_proj (by rw [← Category.assoc, h₁, Category.assoc])
  subst hxy
  cases a <;> cases b <;> cases c <;> cases d <;> simp_all

/-- The local multiplication maps agree on the overlaps of the charts of the fibre square, so
they glue. -/
public lemma productChartMap_compatible (b c b' c' : Bool) :
    pullback.fst (D.productChart b c) (D.productChart b' c') ≫ D.productChartMap b c =
      pullback.snd (D.productChart b c) (D.productChart b' c') ≫ D.productChartMap b' c' := by
  have h := pullback.condition (f := D.productChart b c) (g := D.productChart b' c')
  have h₁ := congrArg (· ≫ pullback.fst D.proj D.proj) h
  have h₂ := congrArg (· ≫ pullback.snd D.proj D.proj) h
  simp only [Category.assoc, D.productChart_comp_fst, D.productChart_comp_snd] at h₁ h₂
  rw [← D.pullback_fst_eq_snd b c, ← D.pullback_fst_eq_snd b' c'] at h₂
  simp only [productChartMap, ← Category.assoc]
  exact D.chart_xor_compatible _ _ b c b' c' h₁ h₂

/-- The multiplication of the group law on the total space of a section cover. -/
public noncomputable def mulMap : pullback D.proj D.proj ⟶ D.total :=
  D.productCover.glueMorphisms (fun p => D.productChartMap p.1 p.2)
    (fun p q => D.productChartMap_compatible p.1 p.2 q.1 q.2)

/-- The chart of `D.productCover` indexed by `(b, c)` is `D.productChart b c`. -/
public lemma productCover_f (b c : Bool) :
    D.productCover.f (b, c) = D.productChart b c := rfl

/-- On the chart indexed by `(b, c)`, the multiplication is `D.productChartMap b c`. -/
public lemma productChart_comp_mulMap (b c : Bool) :
    D.productChart b c ≫ D.mulMap = D.productChartMap b c := by
  have h := Scheme.Cover.ι_glueMorphisms D.productCover
    (fun p => D.productChartMap p.1 p.2)
    (fun p q => D.productChartMap_compatible p.1 p.2 q.1 q.2) (b, c)
  rw [D.productCover_f] at h
  exact h

/-- On each chart of the fibre square, the multiplication followed by the structure morphism
agrees with the first projection followed by the structure morphism. -/
public lemma productChart_comp_mulMap_comp_proj (b c : Bool) :
    D.productChart b c ≫ D.mulMap ≫ D.proj =
      D.productChart b c ≫ pullback.fst D.proj D.proj ≫ D.proj := by
  rw [← Category.assoc, ← Category.assoc, D.productChart_comp_mulMap, D.productChart_comp_fst,
    productChartMap]
  simp only [Category.assoc, D.chart_comp_proj]

/-- The multiplication is a morphism over `S`: followed by the structure morphism it agrees with
the first projection followed by the structure morphism. -/
public lemma mulMap_comp_proj :
    D.mulMap ≫ D.proj = pullback.fst D.proj D.proj ≫ D.proj :=
  D.productCover.hom_ext _ _ fun p => D.productChart_comp_mulMap_comp_proj p.1 p.2

/-- The comparison morphism from the underlying scheme of the square of the total space in the
slice category to the fibre square. -/
public noncomputable abbrev tensorToPullback :
    (D.over ⊗ D.over).left ⟶ pullback D.proj D.proj :=
  tensorLeftToPullback D.over D.over

/-- The comparison morphism followed by the first projection of the fibre square is the first
projection of the tensor square. -/
public lemma tensorToPullback_comp_fst :
    D.tensorToPullback ≫ pullback.fst D.proj D.proj = (fst D.over D.over).left :=
  tensorLeftToPullback_comp_fst _ _

/-- The comparison morphism followed by the second projection of the fibre square is the second
projection of the tensor square. -/
public lemma tensorToPullback_comp_snd :
    D.tensorToPullback ≫ pullback.snd D.proj D.proj = (snd D.over D.over).left :=
  tensorLeftToPullback_comp_snd _ _

/-- The multiplication of the group law, as a morphism in the slice category. -/
public noncomputable def mulHom : D.over ⊗ D.over ⟶ D.over :=
  Over.homMk (D.tensorToPullback ≫ D.mulMap) (by
    rw [over_hom, Category.assoc, D.mulMap_comp_proj, ← Category.assoc,
      D.tensorToPullback_comp_fst]
    exact (fst D.over D.over).w)

/-- The underlying morphism of schemes of `D.mulHom`. -/
public lemma mulHom_left : D.mulHom.left = D.tensorToPullback ≫ D.mulMap := rfl

/-- The inclusion of the piece indexed by a label, namely the corresponding section. -/
public noncomputable def partHom (b : Bool) : Over.mk (𝟙 S) ⟶ D.over :=
  Over.homMk (D.chart b) (D.chart_comp_proj b)

/-- A morphism over `S` into the piece indexed by `b`, composed with its inclusion, has as
underlying morphism the structure morphism of the source followed by the section `D.chart b`. -/
public lemma comp_partHom_left {T : CategoryTheory.Over S} (b : Bool)
    (t : T ⟶ Over.mk (𝟙 S)) : (t ≫ D.partHom b).left = T.hom ≫ D.chart b := by
  have ht : t.left = T.hom := by simpa using t.w
  rw [Over.comp_left, ht]
  rfl

/-- The multiplication sends a pair of points of the pieces indexed by `b` and `c` to the piece
indexed by `b ^^ c`. -/
public lemma lift_partHom_comp_mulHom {T : CategoryTheory.Over S} (b c : Bool)
    (f g : T ⟶ Over.mk (𝟙 S)) :
    lift (f ≫ D.partHom b) (g ≫ D.partHom c) ≫ D.mulHom =
      overUnit T ≫ D.partHom (b ^^ c) := by
  have hcond : T.hom ≫ D.chart b ≫ D.proj = T.hom ≫ D.chart c ≫ D.proj := by
    rw [D.chart_comp_proj, D.chart_comp_proj]
  refine Over.OverMorphism.ext ?_
  rw [Over.comp_left, mulHom_left, ← Category.assoc]
  have hcomp : (lift (f ≫ D.partHom b) (g ≫ D.partHom c)).left ≫ D.tensorToPullback =
      pullback.lift T.hom T.hom hcond ≫ D.productChart b c := by
    refine pullback.hom_ext ?_ ?_
    · rw [Category.assoc, D.tensorToPullback_comp_fst, ← Over.comp_left, lift_fst,
        Category.assoc, D.productChart_comp_fst, ← Category.assoc, pullback.lift_fst]
      exact D.comp_partHom_left b f
    · rw [Category.assoc, D.tensorToPullback_comp_snd, ← Over.comp_left, lift_snd,
        Category.assoc, D.productChart_comp_snd, ← Category.assoc, pullback.lift_snd]
      exact D.comp_partHom_left c g
  rw [hcomp, Category.assoc, D.productChart_comp_mulMap, productChartMap, ← Category.assoc,
    pullback.lift_fst]
  exact (D.comp_partHom_left (b ^^ c) (overUnit T)).symm

/-- Auxiliary to `over_hom_ext`: two morphisms out of `T` agree on the preimage under `f` of the
chart indexed by `b`. -/
public lemma over_hom_ext_aux {T Z : CategoryTheory.Over S} (f : T ⟶ D.over) (g h : T ⟶ Z)
    (H : ∀ (b : Bool) (V : CategoryTheory.Over S) (a : V ⟶ T) (t : V ⟶ Over.mk (𝟙 S)),
      a ≫ f = t ≫ D.partHom b → a ≫ g = a ≫ h) (b : Bool) :
    pullback.fst f.left (D.chart b) ≫ g.left = pullback.fst f.left (D.chart b) ≫ h.left := by
  have hp : pullback.fst f.left (D.chart b) ≫ f.left =
      pullback.snd f.left (D.chart b) ≫ D.chart b := pullback.condition
  have hb : pullback.fst f.left (D.chart b) ≫ T.hom = pullback.snd f.left (D.chart b) := by
    rw [show T.hom = f.left ≫ D.proj from (over_hom D ▸ f.w).symm, ← Category.assoc, hp,
      Category.assoc, D.chart_comp_proj, Category.comp_id]
  refine congrArg CommaMorphism.left
    (H b (Over.mk (pullback.fst f.left (D.chart b) ≫ T.hom))
      (Over.homMk (pullback.fst f.left (D.chart b)) rfl)
      (Over.homMk (pullback.snd f.left (D.chart b)) (by simpa using hb.symm))
      (Over.OverMorphism.ext ?_))
  rw [Over.comp_left, Over.comp_left]
  exact hp

/-- Two morphisms out of `T` agree if they agree after restricting to every part of `T` that `f`
sends into one of the two pieces. -/
public lemma over_hom_ext {T Z : CategoryTheory.Over S} (f : T ⟶ D.over) (g h : T ⟶ Z)
    (H : ∀ (b : Bool) (V : CategoryTheory.Over S) (a : V ⟶ T) (t : V ⟶ Over.mk (𝟙 S)),
      a ≫ f = t ≫ D.partHom b → a ≫ g = a ≫ h) : g = h :=
  Over.OverMorphism.ext (Scheme.Cover.hom_ext (D.cover.pullback₁ f.left) _ _
    fun b => D.over_hom_ext_aux f g h H b)

/-- The presentation of the group law on the total space of a section cover: the two charts are
the two pieces, and multiplication adds their labels modulo two. -/
public noncomputable def xorGroupPresentation : XorGroupPresentation S where
  carrier := D.over
  part _ := Over.mk (𝟙 S)
  mono_part_hom _ := inferInstanceAs (Mono (𝟙 S))
  partHom := D.partHom
  partUnit T := overUnit T
  partMul {T} _ _ _ _ := overUnit T
  mul := D.mulHom
  lift_partHom_comp_mul := fun b c f g => D.lift_partHom_comp_mulHom b c f g
  hom_ext := fun f g h H => D.over_hom_ext f g h H

/-- The group object over `S` carried by the total space of a section cover. -/
@[instance_reducible]
public noncomputable def grpObj : GrpObj D.over :=
  D.xorGroupPresentation.grpObj

/-- Each section followed by the structure morphism satisfies every morphism property that holds
for the identity of `S`. -/
public lemma chart_comp_proj_prop (Q : MorphismProperty Scheme.{u}) (hid : Q (𝟙 S)) (b : Bool) :
    Q (D.chart b ≫ D.proj) := by
  rw [D.chart_comp_proj]
  exact hid

/-- The structure morphism of a section cover satisfies every morphism property that is Zariski
local at the source and holds for identity morphisms. -/
public lemma proj_prop (Q : MorphismProperty Scheme.{u}) (hQ : IsZariskiLocalAtSource Q)
    (hid : Q (𝟙 S)) : Q D.proj := by
  have := hQ
  rw [IsZariskiLocalAtSource.iff_of_openCover (P := Q) D.cover]
  exact fun b => D.chart_comp_proj_prop Q hid b

/-- The total space of a section cover over a compact base is compact. -/
public lemma compactSpace_total [CompactSpace S] : CompactSpace D.total := by
  have himage (b : Bool) : IsCompact (Set.range (D.chart b)) :=
    isCompact_range (D.chart b).continuous
  have hcover : Set.range (D.chart false) ∪ Set.range (D.chart true) =
      (Set.univ : Set D.total) := by
    refine Set.eq_univ_of_forall fun x => ?_
    obtain ⟨b, y, hy⟩ := D.exists_chart_eq x
    cases b
    · exact Set.mem_union_left _ ⟨y, hy⟩
    · exact Set.mem_union_right _ ⟨y, hy⟩
  exact isCompact_univ_iff.mp (hcover ▸ (himage false).union (himage true))

/-- The structure morphism of a section cover over a compact quasi-separated base is
quasi-compact. -/
public lemma quasiCompact_proj [CompactSpace S] [QuasiSeparatedSpace S] :
    QuasiCompact D.proj := by
  have := D.compactSpace_total
  exact quasiCompact_of_compactSpace D.proj

end SectionCoverData

end Stacks.Examples

end
