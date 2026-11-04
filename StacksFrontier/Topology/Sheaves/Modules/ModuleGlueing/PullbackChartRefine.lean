module

public import StacksFrontier.Topology.Sheaves.Modules.ModuleGlueing.PullbackChart

/-!
# The refinement laws of the chart description of an inverse image

`AlgebraicGeometry.Scheme.Modules.pullbackIsoOfRestrictIso` describes the inverse image of a sheaf
of modules along a morphism factoring through an open immersion: if `h = g ≫ f` with `f` an open
immersion and the restriction of `N` along `f` identified with `M` by `e`, then `h^* N` is `g^* M`.
This file proves the two laws relating two such descriptions of one inverse image, which is what a
glueing argument over a cover of charts needs:

* shrinking the *source*, replacing `g` by `κ ≫ g` for a further open immersion `κ`;
* shrinking the *chart*, replacing `f` by a smaller open immersion `f'` factoring through it, given
  a comparison `ν` of the two chart identifications.

Both are instances of the associativity coherence of the inverse-image pseudofunctor, which
`AlgebraicGeometry.Scheme.Modules.pseudofunctor_associativity` of Mathlib supplies; this file first
puts that coherence in component form.

Each law is proved for an arbitrary identification `ε : f^* N ≅ M` of the chart sheaf, through
`AlgebraicGeometry.Scheme.Modules.pullbackChartDesc`, and then specialised to the identification
that comes from an identification of the *restriction*.

## Main results

* `AlgebraicGeometry.Scheme.Modules.pullbackComp_assoc_inv_app`: **the associativity coherence of
  the inverse image, on components.** The two ways of identifying `(a ≫ b ≫ c)^* N` with
  `a^* b^* c^* N` agree.
* `AlgebraicGeometry.Scheme.Modules.pullbackComp_hom_app_pullbackCongr`: the same coherence in the
  form that compares splitting off the last factor of a composite with transporting along a
  congruence in the first factor.
* `AlgebraicGeometry.Scheme.Modules.pullbackChartDesc_precomp`: **the chart description is
  compatible with precomposing the factoring morphism**, and
  `pullbackIsoOfRestrictIso_precomp`, the same for `pullbackIsoOfRestrictIso`.
* `AlgebraicGeometry.Scheme.Modules.pullbackChartDesc_refine` and
  `pullbackIsoOfRestrictIso_refine`: **the chart description is compatible with refining the
  chart.** The hypothesis is that the two chart identifications are related by a morphism `ν` of
  the chart sheaves, which is exactly the chart-refinement law of a glued sheaf.

## Implementation notes

`pullbackComp_assoc_inv_app` is equivalent to `Stacks.Modules.pullbackComp_pentagon` and to
`Stacks.Sites.pullbackComp_assoc_app`, which live in files downstream of the glueing of sheaves of
modules and so are not imported here.

The transport `AlgebraicGeometry.Scheme.Modules.pullbackCongr` along the associativity of
composition is the identity on components, by `rfl` — composition of schemes is definitionally
associative. It cannot be dropped from the *statement* of the coherence, though: without it the two
sides have the types `(a ≫ b ≫ c)^* N` and `((a ≫ b) ≫ c)^* N`, which the elaborator does not
identify at the transparency it type-checks statements at.

No `stacks` attribute is attached: the file states no clause of a tag, it relates two presentations
of one inverse image.

## References

* [Stacks Project, Tag 00AM](https://stacks.math.columbia.edu/tag/00AM)
* [Stacks Project, Tag 01NQ](https://stacks.math.columbia.edu/tag/01NQ)
-/

@[expose] public noncomputable section

open CategoryTheory
open AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.Modules

universe u

/-- **The associativity coherence of the inverse image of sheaves of modules, on components.**
Identifying `(a ≫ b ≫ c)^* N` with `a^* b^* c^* N` by splitting off `c` first and then `b` is the
same as splitting off `b ≫ c` first and then applying `a^*` to the splitting of `c`. -/
public theorem pullbackComp_assoc_inv_app {X Y Z T : Scheme.{u}} (a : X ⟶ Y) (b : Y ⟶ Z)
    (c : Z ⟶ T) (N : T.Modules) :
    (pullbackCongr (Category.assoc a b c)).inv.app N
        ≫ (pullbackComp (a ≫ b) c).inv.app N
        ≫ (pullbackComp a b).inv.app ((pullback c).obj N)
      = (pullbackComp a (b ≫ c)).inv.app N
        ≫ (pullback a).map ((pullbackComp b c).inv.app N) := by
  have key := congrArg (fun z : (pullback (a ≫ b ≫ c) ⟶ pullback ((a ≫ b) ≫ c)) => z.app N)
    (pseudofunctor_associativity a b c)
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.associator_hom_app, Category.id_comp] at key
  rw [← cancel_mono ((pullbackComp a b).hom.app ((pullback c).obj N) ≫
    (pullbackComp (a ≫ b) c).hom.app N)]
  simp only [Category.assoc, Iso.inv_hom_id_app_assoc, Iso.inv_hom_id_app, Category.comp_id]
  rw [key]
  simp [pullbackCongr]

/-- The transport of the inverse image along `rfl` is the identity on components. -/
private theorem pullbackCongr_rfl_hom_app {X Y : Scheme.{u}} {u : X ⟶ Y} (N : Y.Modules) :
    (pullbackCongr (rfl : u = u)).hom.app N = 𝟙 _ := rfl

/-- The inverse of the transport of the inverse image along `rfl` is the identity on components. -/
private theorem pullbackCongr_rfl_inv_app {X Y : Scheme.{u}} {u : X ⟶ Y} (N : Y.Modules) :
    (pullbackCongr (rfl : u = u)).inv.app N = 𝟙 _ := rfl

/-- **The comparison of the inverse image along a composite, under a congruence in the first
factor.** Identifying `(cm ≫ r)^* N` with `k^* (c ≫ r)^* N`, where `k ≫ c = cm`, can be done by
splitting off `r` first and then transporting along the congruence, or by transporting along the
congruence first and then splitting off `c`. -/
public theorem pullbackComp_hom_app_pullbackCongr {A B C D : Scheme.{u}} (k : A ⟶ B) (c : B ⟶ C)
    (r : C ⟶ D) {cm : A ⟶ C} (hk : k ≫ c = cm) (hκ : k ≫ c ≫ r = cm ≫ r) (N : D.Modules) :
    (pullbackCongr hk).inv.app ((pullback r).obj N)
          ≫ (pullbackComp k c).inv.app ((pullback r).obj N)
          ≫ (pullback k).map ((pullbackComp c r).hom.app N)
      = (pullbackComp cm r).hom.app N ≫ (pullbackCongr hκ).inv.app N
          ≫ (pullbackComp k (c ≫ r)).inv.app N := by
  subst hk
  have hco := pullbackComp_assoc_inv_app k c r N
  rw [pullbackCongr_rfl_inv_app, Category.id_comp,
    show (pullbackCongr hκ).inv.app N
      = (pullbackCongr (Category.assoc k c r)).hom.app N from rfl]
  rw [← cancel_epi ((pullbackCongr (Category.assoc k c r)).inv.app N
    ≫ (pullbackComp (k ≫ c) r).inv.app N)]
  simp only [Category.assoc, Iso.inv_hom_id_app_assoc]
  rw [← Category.assoc ((pullbackCongr (Category.assoc k c r)).inv.app N),
    ← Category.assoc ((pullbackCongr (Category.assoc k c r)).inv.app N
      ≫ (pullbackComp (k ≫ c) r).inv.app N),
    show ((pullbackCongr (Category.assoc k c r)).inv.app N
          ≫ (pullbackComp (k ≫ c) r).inv.app N)
        ≫ (pullbackComp k c).inv.app ((pullback r).obj N)
      = (pullbackComp k (c ≫ r)).inv.app N
        ≫ (pullback k).map ((pullbackComp c r).inv.app N) from
      (Category.assoc _ _ _).trans hco]
  simp only [Category.assoc, ← Functor.map_comp, Iso.inv_hom_id_app,
    CategoryTheory.Functor.map_id]
  simp

/-- A functor applied to a composite of four morphisms. -/
public theorem map_comp₄ {D E : Type*} [Category D] [Category E] (F : D ⥤ E)
    {X₀ X₁ X₂ X₃ X₄ : D} (u₁ : X₀ ⟶ X₁) (u₂ : X₁ ⟶ X₂) (u₃ : X₂ ⟶ X₃) (u₄ : X₃ ⟶ X₄) :
    F.map (u₁ ≫ u₂ ≫ u₃ ≫ u₄) = F.map u₁ ≫ F.map u₂ ≫ F.map u₃ ≫ F.map u₄ := by
  simp

/-- Associativity bookkeeping: splitting the last factor off a composite of five. -/
public theorem comp_assoc₅ {D : Type*} [Category D] {X₀ X₁ X₂ X₃ X₄ X₅ : D}
    (u₁ : X₀ ⟶ X₁) (u₂ : X₁ ⟶ X₂) (u₃ : X₂ ⟶ X₃) (u₄ : X₃ ⟶ X₄) (u₅ : X₄ ⟶ X₅) :
    (u₁ ≫ u₂ ≫ u₃ ≫ u₄) ≫ u₅ = u₁ ≫ u₂ ≫ u₃ ≫ u₄ ≫ u₅ := by
  simp

/-- Associativity bookkeeping: splitting the last factor off a composite of six. -/
public theorem comp_assoc₆ {D : Type*} [Category D] {X₀ X₁ X₂ X₃ X₄ X₅ X₆ : D}
    (u₁ : X₀ ⟶ X₁) (u₂ : X₁ ⟶ X₂) (u₃ : X₂ ⟶ X₃) (u₄ : X₃ ⟶ X₄) (u₅ : X₄ ⟶ X₅)
    (u₆ : X₅ ⟶ X₆) :
    u₁ ≫ u₂ ≫ u₃ ≫ u₄ ≫ u₅ ≫ u₆ = (u₁ ≫ u₂ ≫ u₃ ≫ u₄ ≫ u₅) ≫ u₆ := by
  simp

section Spellings

variable {S T Y : Scheme.{u}}

/-- The transport of the inverse image along a symmetric equality, on components, is the inverse
of the transport along the equality. Both are `eqToHom` between the same pair of objects. -/
public theorem pullbackCongr_symm_hom_app {u v : T ⟶ S} (p : u = v) (N : S.Modules) :
    (pullbackCongr p.symm).hom.app N = (pullbackCongr p).inv.app N := rfl

/-- The transport of the inverse image along a symmetric equality, on components, inverted. -/
public theorem pullbackCongr_symm_inv_app {u v : T ⟶ S} (p : u = v) (N : S.Modules) :
    (pullbackCongr p.symm).inv.app N = (pullbackCongr p).hom.app N := rfl

/-- `AlgebraicGeometry.Scheme.Modules.pullbackIsoOfRestrictIso` written out as the three morphisms
it composes. -/
public theorem pullbackIsoOfRestrictIso_hom (f : Y ⟶ S) [IsOpenImmersion f] {N : S.Modules}
    {M : Y.Modules} (e : N.restrict f ≅ M) (g : T ⟶ Y) {h : T ⟶ S} (hfac : h = g ≫ f) :
    (pullbackIsoOfRestrictIso f e g hfac).hom
      = (pullbackCongr hfac).hom.app N ≫ (pullbackComp g f).inv.app N
        ≫ (pullback g).map ((((restrictFunctorIsoPullback f).app N).symm ≪≫ e).hom) := rfl

/-- `AlgebraicGeometry.Scheme.Modules.pullbackIsoOfRestrictIso` inverted, written out as the three
morphisms it composes. -/
public theorem pullbackIsoOfRestrictIso_inv (f : Y ⟶ S) [IsOpenImmersion f] {N : S.Modules}
    {M : Y.Modules} (e : N.restrict f ≅ M) (g : T ⟶ Y) {h : T ⟶ S} (hfac : h = g ≫ f) :
    (pullbackIsoOfRestrictIso f e g hfac).inv
      = (pullback g).map ((((restrictFunctorIsoPullback f).app N).symm ≪≫ e).inv)
        ≫ (pullbackComp g f).hom.app N ≫ (pullbackCongr hfac).inv.app N := by
  simp [pullbackIsoOfRestrictIso]

end Spellings

section ChartDesc

variable {S T T' Y Y' : Scheme.{u}}

/-- **The inverse image along a morphism factoring through a chart, given an identification of the
chart sheaf.** This is `AlgebraicGeometry.Scheme.Modules.pullbackIsoOfRestrictIso` with the
identification of the inverse image along the chart taken as given rather than produced from an
identification of the restriction along it. -/
public def pullbackChartDesc (f : Y ⟶ S) {N : S.Modules} {M : Y.Modules}
    (ε : (pullback f).obj N ≅ M) (g : T ⟶ Y) {h : T ⟶ S} (hfac : h = g ≫ f) :
    (pullback h).obj N ≅ (pullback g).obj M :=
  (pullbackCongr hfac).app N ≪≫ ((pullbackComp g f).app N).symm ≪≫ (pullback g).mapIso ε

/-- `AlgebraicGeometry.Scheme.Modules.pullbackIsoOfRestrictIso` is
`AlgebraicGeometry.Scheme.Modules.pullbackChartDesc` of the identification of the inverse image
along the chart which the identification of the restriction gives. -/
public theorem pullbackIsoOfRestrictIso_eq_pullbackChartDesc (f : Y ⟶ S) [IsOpenImmersion f]
    {N : S.Modules} {M : Y.Modules} (e : N.restrict f ≅ M) (g : T ⟶ Y) {h : T ⟶ S}
    (hfac : h = g ≫ f) :
    pullbackIsoOfRestrictIso f e g hfac
      = pullbackChartDesc f (((restrictFunctorIsoPullback f).app N).symm ≪≫ e) g hfac :=
  rfl

/-- **The chart description of an inverse image is compatible with precomposing the factoring
morphism.** If `h = b ≫ f` factors through the chart `f` and `κ ≫ b = b'`, so that `κ ≫ h = h'`
factors as `b' ≫ f`, then the description of `h'^* N` as `b'^* M` is the inverse image along `κ` of
the description of `h^* N` as `b^* M`, read through the comparisons of the inverse image along a
composite. -/
public theorem pullbackChartDesc_precomp (f : Y ⟶ S) {N : S.Modules} {M : Y.Modules}
    (ε : (pullback f).obj N ≅ M)
    (b : T ⟶ Y) {h : T ⟶ S} (hb : h = b ≫ f)
    (κ : T' ⟶ T) {b' : T' ⟶ Y} (hsq : κ ≫ b = b') {h' : T' ⟶ S} (hκ : κ ≫ h = h')
    (hb' : h' = b' ≫ f) :
    (pullbackCongr hκ).inv.app N ≫ (pullbackComp κ h).inv.app N
          ≫ (pullback κ).map (pullbackChartDesc f ε b hb).hom
          ≫ (pullbackComp κ b).hom.app M ≫ (pullbackCongr hsq).hom.app M
      = (pullbackChartDesc f ε b' hb').hom := by
  subst hb
  subst hsq
  subst hκ
  have hnat := (pullbackComp κ b).hom.naturality ε.hom
  simp only [Functor.comp_map] at hnat
  calc (pullbackCongr (rfl : κ ≫ b ≫ f = κ ≫ b ≫ f)).inv.app N
        ≫ (pullbackComp κ (b ≫ f)).inv.app N
        ≫ (pullback κ).map (pullbackChartDesc f ε b rfl).hom
        ≫ (pullbackComp κ b).hom.app M
        ≫ (pullbackCongr (rfl : κ ≫ b = κ ≫ b)).hom.app M
      = ((pullbackComp κ (b ≫ f)).inv.app N
          ≫ (pullback κ).map ((pullbackComp b f).inv.app N))
        ≫ (pullback κ).map ((pullback b).map ε.hom) ≫ (pullbackComp κ b).hom.app M := by
        simp only [pullbackChartDesc, Iso.trans_hom, Functor.mapIso_hom, Iso.app_hom,
          Functor.map_comp, Category.assoc]
        rw [pullbackCongr_rfl_inv_app, pullbackCongr_rfl_hom_app, pullbackCongr_rfl_hom_app]
        simp
    _ = ((pullbackCongr (Category.assoc κ b f)).inv.app N
          ≫ (pullbackComp (κ ≫ b) f).inv.app N
          ≫ (pullbackComp κ b).inv.app ((pullback f).obj N))
        ≫ (pullback κ).map ((pullback b).map ε.hom) ≫ (pullbackComp κ b).hom.app M := by
        rw [pullbackComp_assoc_inv_app]
    _ = (pullbackChartDesc f ε (κ ≫ b) hb').hom := by
        simp only [Category.assoc, hnat, pullbackChartDesc, Iso.trans_hom, Functor.mapIso_hom,
          Iso.app_hom]
        rw [show (pullbackCongr hb').hom.app N
            = (pullbackCongr (Category.assoc κ b f)).inv.app N from rfl]
        simp

/-- **The chart description is functorial in the identification of the chart sheaf.** -/
public theorem pullbackChartDesc_hom_comp_map (f : Y ⟶ S) {N : S.Modules} {M M' : Y.Modules}
    (ε : (pullback f).obj N ≅ M) (ε' : (pullback f).obj N ≅ M') (ν : M ⟶ M')
    (hν : ε.hom ≫ ν = ε'.hom) (g : T ⟶ Y) {h : T ⟶ S} (hfac : h = g ≫ f) :
    (pullbackChartDesc f ε g hfac).hom ≫ (pullback g).map ν
      = (pullbackChartDesc f ε' g hfac).hom := by
  simp only [pullbackChartDesc, Iso.trans_hom, Functor.mapIso_hom, Iso.app_hom,
    Category.assoc, ← Functor.map_comp, hν]

/-- The chart description through `f` of the inverse image along `b' ≫ l`, cut down along `l`, as
a composite with the inverse image along `b'` of the chart comparison of `l` split off. -/
public theorem pullbackChartDesc_comp_lhs (f : Y ⟶ S) {N : S.Modules} {M : Y.Modules}
    (ε : (pullback f).obj N ≅ M) (l : Y' ⟶ Y) (b' : T ⟶ Y') :
    (pullbackChartDesc f ε (b' ≫ l) rfl).hom
          ≫ (pullbackCongr (rfl : b' ≫ l = b' ≫ l)).inv.app M
          ≫ (pullbackComp b' l).inv.app M
      = ((pullbackComp (b' ≫ l) f).inv.app N
            ≫ (pullbackComp b' l).inv.app ((pullback f).obj N))
          ≫ (pullback b').map ((pullback l).map ε.hom) := by
  have hnat := (pullbackComp b' l).inv.naturality ε.hom
  simp only [Functor.comp_map] at hnat
  simp only [pullbackChartDesc, Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom, Iso.app_inv,
    Iso.app_hom, Category.assoc]
  rw [pullbackCongr_rfl_hom_app, pullbackCongr_rfl_inv_app]
  simp only [Category.id_comp, hnat]

/-- The chart description through the smaller chart `l ≫ f`, whose chart sheaf is the inverse image
along `l` of that of `f`, with that chart comparison split off. -/
public theorem pullbackChartDesc_comp_rhs (f : Y ⟶ S) {N : S.Modules} {M : Y.Modules}
    (ε : (pullback f).obj N ≅ M) (l : Y' ⟶ Y) (b' : T ⟶ Y') :
    (pullbackChartDesc (l ≫ f) (pullbackChartDesc f ε l rfl) b'
          (Category.assoc b' l f)).hom
      = ((pullbackCongr (Category.assoc b' l f)).hom.app N
            ≫ (pullbackComp b' (l ≫ f)).inv.app N
            ≫ (pullback b').map ((pullbackComp l f).inv.app N))
          ≫ (pullback b').map ((pullback l).map ε.hom) := by
  simp only [pullbackChartDesc, Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom, Iso.app_inv,
    Iso.app_hom, Functor.map_comp, Category.assoc]
  rw [pullbackCongr_rfl_hom_app]
  simp

/-- **The chart description of an inverse image is functorial in the tower of charts.** If the
chart `f'` factors through the chart `f` by `l`, then describing `h^* N` through `f` and then
cutting down along `l` is describing it through `f'`, with the chart sheaf of `f'` taken to be the
inverse image along `l` of that of `f`. -/
public theorem pullbackChartDesc_comp (f : Y ⟶ S) {N : S.Modules} {M : Y.Modules}
    (ε : (pullback f).obj N ≅ M) (l : Y' ⟶ Y) {f' : Y' ⟶ S} (hl : f' = l ≫ f)
    (b' : T ⟶ Y') {b : T ⟶ Y} (hg : b' ≫ l = b) {h : T ⟶ S} (hb : h = b ≫ f)
    (hb' : h = b' ≫ f') :
    (pullbackChartDesc f ε b hb).hom ≫ (pullbackCongr hg).inv.app M
          ≫ (pullbackComp b' l).inv.app M
      = (pullbackChartDesc f' (pullbackChartDesc f ε l hl) b' hb').hom := by
  subst hl
  subst hg
  subst hb
  refine Eq.trans (pullbackChartDesc_comp_lhs f ε l b') ?_
  refine Eq.trans ?_ (pullbackChartDesc_comp_rhs f ε l b').symm
  refine eq_whisker ?_ _
  exact ((Category.id_comp _).symm.trans
    (pullbackComp_assoc_inv_app b' l f N)).trans (Category.id_comp _).symm

/-- **The chart description of an inverse image is compatible with refining the chart.** Let the
chart `f'` factor through the chart `f` by `l`, let the chart sheaves of `f` and `f'` be identified
with `M` and `M'` by `ε` and `ε'`, and let `ν` compare the two identifications in the sense that
describing the inverse image along `f'` through `f` and then applying `ν` is `ε'`, which is the
chart-refinement law of a sheaf glued from the charts. Then for a morphism `h` factoring through
`f'`, the description of `h^* N` through `f'` is its description through `f`, cut down along `l`
and pushed through `ν`. -/
public theorem pullbackChartDesc_refine (f : Y ⟶ S) {N : S.Modules} {M : Y.Modules}
    (ε : (pullback f).obj N ≅ M) (l : Y' ⟶ Y) {f' : Y' ⟶ S} (hl : f' = l ≫ f)
    {M' : Y'.Modules} (ε' : (pullback f').obj N ≅ M') (ν : (pullback l).obj M ⟶ M')
    (hν : (pullbackChartDesc f ε l hl).hom ≫ ν = ε'.hom)
    (b' : T ⟶ Y') {b : T ⟶ Y} (hg : b' ≫ l = b) {h : T ⟶ S} (hb : h = b ≫ f)
    (hb' : h = b' ≫ f') :
    (pullbackChartDesc f ε b hb).hom ≫ (pullbackCongr hg).inv.app M
          ≫ (pullbackComp b' l).inv.app M ≫ (pullback b').map ν
      = (pullbackChartDesc f' ε' b' hb').hom := by
  refine Eq.trans (Category.assoc _ _ _).symm ?_
  refine Eq.trans (Category.assoc _ _ _).symm ?_
  refine Eq.trans (eq_whisker ((Category.assoc _ _ _).trans
    (pullbackChartDesc_comp f ε l hl b' hg hb hb')) _) ?_
  exact pullbackChartDesc_hom_comp_map f' _ ε' ν hν b' hb'

/-- `AlgebraicGeometry.Scheme.Modules.pullbackChartDesc_refine` for
`AlgebraicGeometry.Scheme.Modules.pullbackIsoOfRestrictIso`, whose chart identification comes from
an identification of the restriction along the chart. -/
public theorem pullbackIsoOfRestrictIso_refine (f : Y ⟶ S) [IsOpenImmersion f] {N : S.Modules}
    {M : Y.Modules} (e : N.restrict f ≅ M) (l : Y' ⟶ Y) {f' : Y' ⟶ S} [IsOpenImmersion f']
    (hl : f' = l ≫ f) {M' : Y'.Modules} (e' : N.restrict f' ≅ M')
    (ν : (pullback l).obj M ⟶ M')
    (hν : (pullbackIsoOfRestrictIso f e l hl).hom ≫ ν
      = (((restrictFunctorIsoPullback f').app N).symm ≪≫ e').hom)
    (b' : T ⟶ Y') {b : T ⟶ Y} (hg : b' ≫ l = b) {h : T ⟶ S} (hb : h = b ≫ f)
    (hb' : h = b' ≫ f') :
    (pullbackIsoOfRestrictIso f e b hb).hom ≫ (pullbackCongr hg).inv.app M
          ≫ (pullbackComp b' l).inv.app M ≫ (pullback b').map ν
      = (pullbackIsoOfRestrictIso f' e' b' hb').hom :=
  pullbackChartDesc_refine f _ l hl (((restrictFunctorIsoPullback f').app N).symm ≪≫ e') ν hν
    b' hg hb hb'

/-- `AlgebraicGeometry.Scheme.Modules.pullbackChartDesc_precomp` for
`AlgebraicGeometry.Scheme.Modules.pullbackIsoOfRestrictIso`. -/
public theorem pullbackIsoOfRestrictIso_precomp (f : Y ⟶ S) [IsOpenImmersion f]
    {N : S.Modules} {M : Y.Modules} (e : N.restrict f ≅ M)
    (b : T ⟶ Y) {h : T ⟶ S} (hb : h = b ≫ f)
    (κ : T' ⟶ T) {b' : T' ⟶ Y} (hsq : κ ≫ b = b') {h' : T' ⟶ S} (hκ : κ ≫ h = h')
    (hb' : h' = b' ≫ f) :
    (pullbackCongr hκ).inv.app N ≫ (pullbackComp κ h).inv.app N
          ≫ (pullback κ).map (pullbackIsoOfRestrictIso f e b hb).hom
          ≫ (pullbackComp κ b).hom.app M ≫ (pullbackCongr hsq).hom.app M
      = (pullbackIsoOfRestrictIso f e b' hb').hom :=
  pullbackChartDesc_precomp f _ b hb κ hsq hκ hb'

/-! ### The nested case of a glueing of chart members -/

section Nested

variable {X' Y Z₁ Z₂ W : Scheme.{u}} {M₀ : Y.Modules} (r : X' ⟶ Y)
  (d : W ⟶ Y) [IsOpenImmersion d] {MW : W.Modules} (eB : M₀.restrict d ≅ MW)
  {N' : X'.Modules}
  (c₂ : Z₂ ⟶ X') [IsOpenImmersion c₂] {MZ₂ : Z₂.Modules} (e'₂ : N'.restrict c₂ ≅ MZ₂)
  {c₁ : Z₁ ⟶ X'} [IsOpenImmersion c₁] (k : Z₁ ⟶ Z₂) (hkc : k ≫ c₂ = c₁)
  {MZ₁ : Z₁.Modules} (e'₁ : N'.restrict c₁ ≅ MZ₁)
  (b₂ : Z₂ ⟶ W) (hfac₂ : c₂ ≫ r = b₂ ≫ d)
  {b₁ : Z₁ ⟶ W} (hsq : k ≫ b₂ = b₁) (hfac₁ : c₁ ≫ r = b₁ ≫ d)
  (mm₂ : (pullback b₂).obj MW ⟶ MZ₂) (mm₁ : (pullback b₁).obj MW ⟶ MZ₁)
  (ν : (pullback k).obj MZ₂ ⟶ MZ₁)

include hkc in
omit [IsOpenImmersion c₂] [IsOpenImmersion c₁] in
/-- The chart `c₁` followed by `r`, factored through `c₂ ≫ r`. -/
public theorem comp_comp_eq_of_chart : k ≫ c₂ ≫ r = c₁ ≫ r :=
  (Category.assoc _ _ _).symm.trans (congrArg (fun z => z ≫ r) hkc)

include hkc hsq in
omit [IsOpenImmersion c₂] [IsOpenImmersion c₁] in
/-- **The chart descriptions of `M₀` pulled back along the two charts of `X'` are related by the
comparisons of the inverse image along a composite.** -/
public theorem pullbackComp_comp_pullbackIsoOfRestrictIso :
    (pullbackCongr hkc).inv.app ((pullback r).obj M₀)
        ≫ (pullbackComp k c₂).inv.app ((pullback r).obj M₀)
        ≫ (pullback k).map ((pullbackComp c₂ r).hom.app M₀)
        ≫ (pullback k).map ((pullbackIsoOfRestrictIso d eB b₂ hfac₂).hom)
        ≫ (pullbackComp k b₂).hom.app MW
        ≫ (pullbackCongr hsq).hom.app MW
      = (pullbackComp c₁ r).hom.app M₀ ≫ (pullbackIsoOfRestrictIso d eB b₁ hfac₁).hom := by
  have hL3 := pullbackComp_hom_app_pullbackCongr k c₂ r hkc
    (comp_comp_eq_of_chart r c₂ k hkc) M₀
  have hpre := pullbackIsoOfRestrictIso_precomp d eB b₂ hfac₂ k hsq
    (comp_comp_eq_of_chart r c₂ k hkc) hfac₁
  rw [reassoc_of% hL3, hpre]

include hkc in
/-- **The tail of the chart member over the larger chart, read on the smaller one, is the
comparison `ν` of the chart sheaves.** This is the chart-refinement law `hν` of the glueing of `N'`
solved for `ν`. -/
public theorem chartTail_comp_comparison
    (hν : (pullbackIsoOfRestrictIso c₂ e'₂ k hkc.symm).hom ≫ ν
      = (((restrictFunctorIsoPullback c₁).app N').symm ≪≫ e'₁).hom) :
    (pullback k).map ((((restrictFunctorIsoPullback c₂).app N').symm ≪≫ e'₂).inv)
        ≫ (pullbackComp k c₂).hom.app N' ≫ (pullbackCongr hkc).hom.app N'
        ≫ (((restrictFunctorIsoPullback c₁).app N').symm ≪≫ e'₁).hom
      = ν := by
  have hinv : (pullbackIsoOfRestrictIso c₂ e'₂ k hkc.symm).inv
      = (pullback k).map ((((restrictFunctorIsoPullback c₂).app N').symm ≪≫ e'₂).inv)
        ≫ (pullbackComp k c₂).hom.app N' ≫ (pullbackCongr hkc).hom.app N' :=
    (pullbackIsoOfRestrictIso_inv c₂ e'₂ _ hkc.symm).trans
      (whisker_eq _ (whisker_eq _ (pullbackCongr_symm_inv_app hkc N')))
  refine Eq.trans ?_ ((Iso.inv_comp_eq _).mpr hν.symm)
  exact ((Category.assoc _ _ _).trans (whisker_eq _ (Category.assoc _ _ _))).symm.trans
    (eq_whisker hinv.symm _)

include hkc hsq in
/-- `AlgebraicGeometry.Scheme.Modules.chartMember_comp_chartIso` with the inverse image of the
chart member distributed over its four factors. -/
public theorem chartMemberSplit
    (hν : (pullbackIsoOfRestrictIso c₂ e'₂ k hkc.symm).hom ≫ ν
      = (((restrictFunctorIsoPullback c₁).app N').symm ≪≫ e'₁).hom)
    (hmm : (pullback k).map mm₂ ≫ ν
      = (pullbackComp k b₂).hom.app MW ≫ (pullbackCongr hsq).hom.app MW ≫ mm₁) :
    (pullbackCongr hkc).inv.app ((pullback r).obj M₀)
        ≫ (pullbackComp k c₂).inv.app ((pullback r).obj M₀)
        ≫ (pullback k).map ((pullbackComp c₂ r).hom.app M₀)
        ≫ (pullback k).map ((pullbackIsoOfRestrictIso d eB b₂ hfac₂).hom)
        ≫ (pullback k).map mm₂
        ≫ (pullback k).map ((((restrictFunctorIsoPullback c₂).app N').symm ≪≫ e'₂).inv)
        ≫ (pullbackComp k c₂).hom.app N' ≫ (pullbackCongr hkc).hom.app N'
        ≫ (((restrictFunctorIsoPullback c₁).app N').symm ≪≫ e'₁).hom
      = (pullbackComp c₁ r).hom.app M₀
        ≫ (pullbackIsoOfRestrictIso d eB b₁ hfac₁).hom ≫ mm₁ := by
  refine Eq.trans (whisker_eq _ (whisker_eq _ (whisker_eq _ (whisker_eq _ (whisker_eq _
    (chartTail_comp_comparison c₂ e'₂ k hkc e'₁ ν hν)))))) ?_
  refine Eq.trans (whisker_eq _ (whisker_eq _ (whisker_eq _ (whisker_eq _ hmm)))) ?_
  refine Eq.trans ?_ (Category.assoc _ _ _)
  refine Eq.trans ?_ (eq_whisker (pullbackComp_comp_pullbackIsoOfRestrictIso r d eB c₂ k hkc
    b₂ hfac₂ hsq hfac₁) _)
  exact comp_assoc₆ _ _ _ _ _ _

include hkc hsq in
/-- **The chart member over the larger chart, pulled back to the smaller one and followed by the
chart identification of `N'` there.** -/
public theorem chartMember_comp_chartIso
    (hν : (pullbackIsoOfRestrictIso c₂ e'₂ k hkc.symm).hom ≫ ν
      = (((restrictFunctorIsoPullback c₁).app N').symm ≪≫ e'₁).hom)
    (hmm : (pullback k).map mm₂ ≫ ν
      = (pullbackComp k b₂).hom.app MW ≫ (pullbackCongr hsq).hom.app MW ≫ mm₁) :
    (pullbackCongr hkc).inv.app ((pullback r).obj M₀)
        ≫ (pullbackComp k c₂).inv.app ((pullback r).obj M₀)
        ≫ (pullback k).map ((pullbackComp c₂ r).hom.app M₀
            ≫ (pullbackIsoOfRestrictIso d eB b₂ hfac₂).hom ≫ mm₂
            ≫ (((restrictFunctorIsoPullback c₂).app N').symm ≪≫ e'₂).inv)
        ≫ (pullbackComp k c₂).hom.app N' ≫ (pullbackCongr hkc).hom.app N'
        ≫ (((restrictFunctorIsoPullback c₁).app N').symm ≪≫ e'₁).hom
      = (pullbackComp c₁ r).hom.app M₀
        ≫ (pullbackIsoOfRestrictIso d eB b₁ hfac₁).hom ≫ mm₁ := by
  refine Eq.trans (whisker_eq _ (whisker_eq _ (eq_whisker (map_comp₄ _ _ _ _ _) _))) ?_
  refine Eq.trans (whisker_eq _ (whisker_eq _ (comp_assoc₅ _ _ _ _ _))) ?_
  exact chartMemberSplit r d eB c₂ e'₂ k hkc e'₁ b₂ hfac₂ hsq hfac₁ mm₂ mm₁ ν hν hmm

include hkc hsq in
/-- **The chart member of a comparison over a smaller chart is the inverse image of the one over
the larger chart.** This is the hypothesis `hφ` of
`Stacks.AlgebraicGeometry.ModuleHomGlue.localApp_ofPullback_eq` for two charts of `X'` one of which
factors through the other, and so the nested case of a glueing of chart members.

The data is: a sheaf `M₀` on `Y` described on a chart `d` of `Y` by `eB`, a sheaf `N'` on `X'`
described on two charts `c₂` and `c₁ = k ≫ c₂` of `X'` by `e'₂` and `e'₁`, a morphism `r : X' ⟶ Y`
whose composites with the two charts factor through `d` by `b₂` and `b₁ = k ≫ b₂`, and comparisons
`mm₂`, `mm₁` of the chart sheaves over the two charts with the chart sheaf of `M₀`. The hypotheses
are the chart-refinement law `hν` of `N'` and the composition law `hmm` of the comparisons; the
comparison `ν` of the chart sheaves of `N'` is what the first contributes and the second
consumes. -/
public theorem chartMember_pullback_eq
    (hν : (pullbackIsoOfRestrictIso c₂ e'₂ k hkc.symm).hom ≫ ν
      = (((restrictFunctorIsoPullback c₁).app N').symm ≪≫ e'₁).hom)
    (hmm : (pullback k).map mm₂ ≫ ν
      = (pullbackComp k b₂).hom.app MW ≫ (pullbackCongr hsq).hom.app MW ≫ mm₁) :
    (pullbackCongr hkc).inv.app ((pullback r).obj M₀)
        ≫ (pullbackComp k c₂).inv.app ((pullback r).obj M₀)
        ≫ (pullback k).map ((pullbackComp c₂ r).hom.app M₀
            ≫ (pullbackIsoOfRestrictIso d eB b₂ hfac₂).hom ≫ mm₂
            ≫ (((restrictFunctorIsoPullback c₂).app N').symm ≪≫ e'₂).inv)
        ≫ (pullbackComp k c₂).hom.app N' ≫ (pullbackCongr hkc).hom.app N'
      = (pullbackComp c₁ r).hom.app M₀
        ≫ (pullbackIsoOfRestrictIso d eB b₁ hfac₁).hom ≫ mm₁
        ≫ (((restrictFunctorIsoPullback c₁).app N').symm ≪≫ e'₁).inv := by
  refine Eq.trans (Category.comp_id _).symm ?_
  refine Eq.trans (whisker_eq _
    (Iso.hom_inv_id (((restrictFunctorIsoPullback c₁).app N').symm ≪≫ e'₁)).symm) ?_
  refine Eq.trans (Category.assoc _ _ _).symm ?_
  refine Eq.trans (eq_whisker (chartMember_comp_chartIso r d eB c₂ e'₂ k hkc e'₁ b₂ hfac₂
    hsq hfac₁ mm₂ mm₁ ν hν hmm) _) ?_
  exact (Category.assoc _ _ _).trans (whisker_eq _ (Category.assoc _ _ _))

end Nested

end ChartDesc

end AlgebraicGeometry.Scheme.Modules

end
