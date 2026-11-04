module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteLocallyFree
public import StacksFrontier.AlgebraicGeometry.Spaces.Flat
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentabilityCriteria
public import StacksFrontier.AlgebraicGeometry.Stacks.Criteria.RestrictionOfScalarsCartesian
public import StacksFrontier.AlgebraicGeometry.Stacks.Criteria.RestrictionOfScalarsEtale

/-!
# Étale coverings and the relative morphism functor (Stacks 05Y5)

Let `S` be a scheme contained in a big fppf site, let `z : Z ⟶ Q` and `x' : X' ⟶ X ⟶ Q` be
morphisms of algebraic spaces over `S` — the source writes the base `Q` as `B`, a name that here
belongs to the site — and let `Mor_Q(Z, X)` be the relative morphism functor of Stacks 05Y2.
Stacks 05Y5 asserts, for `X' ⟶ X` étale and `Z ⟶ Q` finite locally free, that

```text
Mor_Q(Z, X') ⟶ Mor_Q(Z, X)
```

is representable by algebraic spaces and étale, and that it is surjective when `X' ⟶ X` is.

The three theorems below take as hypotheses the predicates
`AlgebraicGeometry.Space.IsFibreSectionsAlgebraicEtale` and
`AlgebraicGeometry.Space.IsFibreSectionsSurjective`, which state Stacks 05XR and Stacks 05XQ for
the fibre data `W ⟶ Z_U ⟶ U` of a scheme-valued point.

## Main definitions

* `AlgebraicGeometry.Space.relativeHomOfPairs`: the morphism into a relative morphism functor
  defined by a family of pairs of Stacks 05Y1 compatible with base change.
* `AlgebraicGeometry.Space.relativeHomPoint`: the scheme-valued point of `Mor_Q(Z, X)` determined
  by a pair of Stacks 05Y1 over a scheme.
* `AlgebraicGeometry.Space.RelativeMorphism.fibreBase`,
  `AlgebraicGeometry.Space.RelativeMorphism.fibreBaseMap`,
  `AlgebraicGeometry.Space.RelativeMorphism.fibreTotal` and
  `AlgebraicGeometry.Space.RelativeMorphism.fibreTotalMap`: the data `W ⟶ Z_U ⟶ U` attached to a
  pair of Stacks 05Y1 over a scheme `U`.
* `AlgebraicGeometry.Space.RelativeMorphism.fibreSections`: the restriction of scalars
  `Res_{Z_U/U}(W)` of that data, which is the functor of sections of Stacks 05XR.
* `AlgebraicGeometry.Space.RelativeMorphism.ofFibrePair` and
  `AlgebraicGeometry.Space.RelativeMorphism.toFibrePair`: the two directions of the identification
  of a section with a lifted pair.
* `AlgebraicGeometry.Space.relativeHomFibreMap`: the induced morphism
  `Res_{Z_U/U}(W) ⟶ Mor_Q(Z, X')`.
* `AlgebraicGeometry.Space.relativeHomFibreComparison` and
  `AlgebraicGeometry.Space.relativeHomFibreIso`: the comparison morphism to the fibre product and
  the isomorphism it is.

## Main results

* `AlgebraicGeometry.Space.isIso_relativeHomFibreComparison`: the fibre of
  `Mor_Q(Z, X') ⟶ Mor_Q(Z, X)` at a scheme-valued point is `Res_{Z_U/U}(W)`.
* `AlgebraicGeometry.Space.isRepresentableByAlgebraicSpaces_relativeHomPostcompose`:
  **Stacks 05Y5**, representability by algebraic spaces.
* `AlgebraicGeometry.Space.hasProperty_isEtale_relativeHomPostcompose`: **Stacks 05Y5**,
  étaleness.
* `AlgebraicGeometry.Space.isSurjective_relativeHomPostcompose`: **Stacks 05Y5**, surjectivity
  when `X' ⟶ X` is surjective.

## References

* [Stacks Project, Tag 05Y5](https://stacks.math.columbia.edu/tag/05Y5)
* [Stacks Project, Tag 05XQ](https://stacks.math.columbia.edu/tag/05XQ)
* [Stacks Project, Tag 05XR](https://stacks.math.columbia.edu/tag/05XR)
* [Stacks Project, Tag 05Y2](https://stacks.math.columbia.edu/tag/05Y2)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-! ### Morphisms into a relative morphism functor -/

/-- A family of pairs of Stacks 05Y1, one for every point of a presheaf `W` and compatible with
base change, defines a morphism `W ⟶ Mor_Q(Z, X)`. -/
noncomputable def relativeHomOfPairs {Z X Q : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {z : Z ⟶ Q}
    {x : X ⟶ Q} (H : RelativeHomConstruction B S hS Z X Q z x)
    {W : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (P : ∀ T : (BigFppfOver B S hS)ᵒᵖ,
      W.obj T → RelativeMorphism B S hS Z X Q z x (yoneda.obj T.unop))
    (hP : ∀ {T U : (BigFppfOver B S hS)ᵒᵖ} (f : T ⟶ U) (w : W.obj T),
      P U (W.map f w) = RelativeMorphism.restrict (yoneda.map f.unop) (P T w)) :
    W ⟶ H.functor where
  app T := ↾fun w => (H.sections T.unop).symm (P T w)
  naturality T U f := by
    ext w
    refine (H.sections U.unop).injective ?_
    change H.sections U.unop ((H.sections U.unop).symm (P U (W.map f w))) =
      H.sections U.unop (H.functor.map f ((H.sections T.unop).symm (P T w)))
    rw [Equiv.apply_symm_apply, H.sections_map_eq, Equiv.apply_symm_apply, hP]

/-- The pair attached to a section of a morphism built from a family of pairs is that family's
value. -/
@[simp]
theorem sections_relativeHomOfPairs {Z X Q : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {z : Z ⟶ Q}
    {x : X ⟶ Q} (H : RelativeHomConstruction B S hS Z X Q z x)
    {W : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (P : ∀ T : (BigFppfOver B S hS)ᵒᵖ,
      W.obj T → RelativeMorphism B S hS Z X Q z x (yoneda.obj T.unop))
    (hP : ∀ {T U : (BigFppfOver B S hS)ᵒᵖ} (f : T ⟶ U) (w : W.obj T),
      P U (W.map f w) = RelativeMorphism.restrict (yoneda.map f.unop) (P T w))
    (T : (BigFppfOver B S hS)ᵒᵖ) (w : W.obj T) :
    H.sections T.unop ((relativeHomOfPairs H P hP).app T w) = P T w :=
  Equiv.apply_symm_apply _ _

/-- **The pair at a scheme-valued point of a relative morphism functor, restricted along a
morphism of the site.** -/
theorem RelativeHomConstruction.sections_app {Z X Q : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {z : Z ⟶ Q} {x : X ⟶ Q} (H : RelativeHomConstruction B S hS Z X Q z x)
    {U T : BigFppfOver B S hS} (ξ : yoneda.obj U ⟶ H.functor) (s : T ⟶ U) :
    H.sections T (ξ.app (op T) s) =
      RelativeMorphism.restrict (yoneda.map s) (H.sections U (yonedaEquiv ξ)) := by
  have h : ξ.app (op T) s = H.functor.map s.op (yonedaEquiv ξ) := by
    conv_lhs => rw [← Equiv.symm_apply_apply yonedaEquiv ξ]
    exact yonedaEquiv_symm_app_apply (yonedaEquiv ξ) (op T) s
  rw [h]
  exact H.sections_map_eq s.op (yonedaEquiv ξ)

/-- The scheme-valued point of `Mor_Q(Z, X)` determined by a pair of Stacks 05Y1 over a
scheme `U`. -/
noncomputable abbrev relativeHomPoint {Z X Q : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {z : Z ⟶ Q}
    {x : X ⟶ Q} (H : RelativeHomConstruction B S hS Z X Q z x) {U : BigFppfOver B S hS}
    (p : RelativeMorphism B S hS Z X Q z x (yoneda.obj U)) : yoneda.obj U ⟶ H.functor :=
  yonedaEquiv.symm ((H.sections U).symm p)

/-- The pair of `AlgebraicGeometry.Space.relativeHomPoint`. -/
@[simp]
theorem sections_relativeHomPoint {Z X Q : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {z : Z ⟶ Q}
    {x : X ⟶ Q} (H : RelativeHomConstruction B S hS Z X Q z x) {U : BigFppfOver B S hS}
    (p : RelativeMorphism B S hS Z X Q z x (yoneda.obj U)) :
    H.sections U (yonedaEquiv (relativeHomPoint H p)) = p := by
  rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply]

/-- The pair of a scheme-valued point of `Mor_Q(Z, X)` determines the point. -/
theorem relativeHomPoint_sections {Z X Q : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {z : Z ⟶ Q}
    {x : X ⟶ Q} (H : RelativeHomConstruction B S hS Z X Q z x) {U : BigFppfOver B S hS}
    (ξ : yoneda.obj U ⟶ H.functor) :
    relativeHomPoint H (H.sections U (yonedaEquiv ξ)) = ξ := by
  show (yonedaEquiv.symm ((H.sections U).symm (H.sections U (yonedaEquiv ξ))) :
    yoneda.obj U ⟶ H.functor) = ξ
  rw [Equiv.symm_apply_apply, Equiv.symm_apply_apply]

/-! ### The fibre data of a pair -/

section Fibre

variable {X' X Z Q : AlgebraicSpaces B S hS} {x' : X' ⟶ Q} {x : X ⟶ Q} {z : Z ⟶ Q}
  {U : BigFppfOver B S hS}

/-- The base change `Z_U = U ×_{a, Q} Z` of `z : Z ⟶ Q` along the first component `a` of a pair of
Stacks 05Y1 over a scheme `U`. -/
noncomputable abbrev RelativeMorphism.fibreBase
    (p : RelativeMorphism B S hS Z.obj X.obj Q.obj z.hom x.hom (yoneda.obj U)) :
    AlgebraicSpaces B S hS :=
  ⟨pullback p.base z.hom,
    isAlgebraicSpace_pullback B S hS p.base z.hom (isAlgebraicSpace_yoneda B S hS U)
      Z.property Q.property⟩

/-- The structure morphism `Z_U ⟶ U` of `AlgebraicGeometry.Space.RelativeMorphism.fibreBase`. -/
noncomputable abbrev RelativeMorphism.fibreBaseMap
    (p : RelativeMorphism B S hS Z.obj X.obj Q.obj z.hom x.hom (yoneda.obj U)) :
    p.fibreBase ⟶ (⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩ : AlgebraicSpaces B S hS) :=
  ObjectProperty.homMk (pullback.fst p.base z.hom)

/-- The fibre `W = Z_U ×_{b, X} X'` of `g : X' ⟶ X` over the second component `b` of a pair of
Stacks 05Y1 over a scheme `U`. -/
noncomputable abbrev RelativeMorphism.fibreTotal (g : X' ⟶ X)
    (p : RelativeMorphism B S hS Z.obj X.obj Q.obj z.hom x.hom (yoneda.obj U)) :
    AlgebraicSpaces B S hS :=
  ⟨pullback p.morphism g.hom,
    isAlgebraicSpace_pullback B S hS p.morphism g.hom p.fibreBase.property X'.property
      X.property⟩

/-- The morphism `W ⟶ Z_U` of `AlgebraicGeometry.Space.RelativeMorphism.fibreTotal`. -/
noncomputable abbrev RelativeMorphism.fibreTotalMap (g : X' ⟶ X)
    (p : RelativeMorphism B S hS Z.obj X.obj Q.obj z.hom x.hom (yoneda.obj U)) :
    p.fibreTotal g ⟶ p.fibreBase :=
  ObjectProperty.homMk (pullback.fst p.morphism g.hom)

/-- The restriction of scalars `Res_{Z_U/U}(W)` of the fibre data of a pair: the functor of
sections of `W ⟶ Z_U` over `U` studied in Stacks 05XR. -/
noncomputable abbrev RelativeMorphism.fibreSections (g : X' ⟶ X)
    (p : RelativeMorphism B S hS Z.obj X.obj Q.obj z.hom x.hom (yoneda.obj U)) :
    RestrictionOfScalarsConstruction B S hS (p.fibreTotalMap g) p.fibreBaseMap :=
  restrictionOfScalars B S hS (p.fibreTotalMap g) p.fibreBaseMap

/-- **A section of `W_T → (Z_U)_T` is a pair of `Mor_Q(Z, X')` lying over the given pair of
`Mor_Q(Z, X)`.** The first component is the composite `T ⟶ U ⟶ Q`, and the second is the
projection of the section to `X'`, read through the identification of `T ×_U Z_U` with
`T ×_Q Z`. -/
noncomputable abbrev RelativeMorphism.ofFibrePair (g : X' ⟶ X) (hg : g.hom ≫ x.hom = x'.hom)
    (p : RelativeMorphism B S hS Z.obj X.obj Q.obj z.hom x.hom (yoneda.obj U))
    {T : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (q : RestrictionPair B S hS (p.fibreTotalMap g) p.fibreBaseMap T) :
    RelativeMorphism B S hS Z.obj X'.obj Q.obj z.hom x'.hom T where
  base := q.base ≫ p.base
  morphism :=
    (pullbackBaseChangeIso p.base z.hom q.base).inv ≫ q.lift ≫ pullback.snd p.morphism g.hom
  commutes := by
    have h1 : q.lift ≫ pullback.fst p.morphism g.hom =
        pullback.snd q.base (pullback.fst p.base z.hom) := q.over
    have h2 : q.lift ≫ pullback.snd p.morphism g.hom ≫ x'.hom =
        pullback.snd q.base (pullback.fst p.base z.hom) ≫
          pullback.snd p.base z.hom ≫ z.hom := by
      rw [← hg, ← Category.assoc (pullback.snd p.morphism g.hom), ← pullback.condition,
        Category.assoc, ← Category.assoc q.lift, h1, p.commutes]
    have h3 : ((pullbackBaseChangeIso p.base z.hom q.base).inv ≫
          pullback.snd q.base (pullback.fst p.base z.hom) ≫ pullback.snd p.base z.hom) ≫
            z.hom =
        pullback.snd (q.base ≫ p.base) z.hom ≫ z.hom :=
      congrArg (fun k => k ≫ z.hom) (pullbackBaseChangeIso_inv_snd p.base z.hom q.base)
    rw [Category.assoc, Category.assoc, h2,
      ← Category.assoc (pullback.snd q.base (pullback.fst p.base z.hom)), ← Category.assoc, h3]

/-- The first component of `AlgebraicGeometry.Space.RelativeMorphism.ofFibrePair`. -/
@[simp]
theorem RelativeMorphism.ofFibrePair_base (g : X' ⟶ X) (hg : g.hom ≫ x.hom = x'.hom)
    (p : RelativeMorphism B S hS Z.obj X.obj Q.obj z.hom x.hom (yoneda.obj U))
    {T : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (q : RestrictionPair B S hS (p.fibreTotalMap g) p.fibreBaseMap T) :
    (p.ofFibrePair g hg q).base = q.base ≫ p.base := rfl

/-- The second component of `AlgebraicGeometry.Space.RelativeMorphism.ofFibrePair`. -/
@[simp]
theorem RelativeMorphism.ofFibrePair_morphism (g : X' ⟶ X) (hg : g.hom ≫ x.hom = x'.hom)
    (p : RelativeMorphism B S hS Z.obj X.obj Q.obj z.hom x.hom (yoneda.obj U))
    {T : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (q : RestrictionPair B S hS (p.fibreTotalMap g) p.fibreBaseMap T) :
    (p.ofFibrePair g hg q).morphism =
      (pullbackBaseChangeIso p.base z.hom q.base).inv ≫
        q.lift ≫ pullback.snd p.morphism g.hom := rfl

/-- **`AlgebraicGeometry.Space.RelativeMorphism.ofFibrePair` commutes with base change.** -/
theorem RelativeMorphism.ofFibrePair_eq_restrict (g : X' ⟶ X) (hg : g.hom ≫ x.hom = x'.hom)
    (p : RelativeMorphism B S hS Z.obj X.obj Q.obj z.hom x.hom (yoneda.obj U))
    {T T' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {f : T' ⟶ T}
    {q : RestrictionPair B S hS (p.fibreTotalMap g) p.fibreBaseMap T}
    {q' : RestrictionPair B S hS (p.fibreTotalMap g) p.fibreBaseMap T'}
    (h : RestrictionPair.IsPullbackAlong f q q') :
    p.ofFibrePair g hg q' = RelativeMorphism.restrict f (p.ofFibrePair g hg q) := by
  obtain ⟨hbase, c₀, hc₁, hc₂, hlift⟩ := h
  have hbase' : q'.base ≫ p.base = f ≫ q.base ≫ p.base := by
    rw [hbase, Category.assoc]
  have hm₀ : (q'.base ≫ p.base) ≫ 𝟙 Q.obj = f ≫ q.base ≫ p.base := by
    rw [Category.comp_id, hbase']
  let m := pullback.map (q'.base ≫ p.base) z.hom (q.base ≫ p.base) z.hom f (𝟙 Z.obj) (𝟙 Q.obj)
    hm₀ (by simp)
  have hm₁ := pullback.map_fst (q'.base ≫ p.base) z.hom (q.base ≫ p.base) z.hom f (𝟙 Z.obj)
    (𝟙 Q.obj) hm₀ (by simp)
  have hm₂ : m ≫ pullback.snd (q.base ≫ p.base) z.hom = pullback.snd (q'.base ≫ p.base) z.hom := by
    rw [pullback.map_snd, Category.comp_id]
  refine RelativeMorphism.eq_restrict_of_comparison hbase' ⟨m, hm₁, hm₂, ?_⟩
  have hnat := pullbackBaseChangeIso_inv_naturality p.base z.hom q.base q'.base f c₀ hc₁ hc₂
    m hm₁ hm₂
  rw [RelativeMorphism.ofFibrePair_morphism, RelativeMorphism.ofFibrePair_morphism, hlift]
  simp only [Category.assoc]
  rw [← Category.assoc (pullbackBaseChangeIso p.base z.hom q'.base).inv c₀, hnat]
  simp only [Category.assoc]

/-- **The pairs of `AlgebraicGeometry.Space.RelativeMorphism.ofFibrePair` are compatible with the
restriction maps of `Res_{Z_U/U}(W)`.** -/
theorem RelativeMorphism.ofFibrePair_natural (g : X' ⟶ X) (hg : g.hom ≫ x.hom = x'.hom)
    (p : RelativeMorphism B S hS Z.obj X.obj Q.obj z.hom x.hom (yoneda.obj U)) :
    ∀ {T T' : (BigFppfOver B S hS)ᵒᵖ} (f : T ⟶ T')
      (v : (p.fibreSections g).presheaf.obj T),
      p.ofFibrePair g hg ((p.fibreSections g).pairEquiv T'.unop
          ((p.fibreSections g).presheaf.map f v)) =
        RelativeMorphism.restrict (yoneda.map f.unop)
          (p.ofFibrePair g hg ((p.fibreSections g).pairEquiv T.unop v)) :=
  fun f v => p.ofFibrePair_eq_restrict g hg ((p.fibreSections g).natural f.unop v)

variable (HX' : RelativeHomConstruction B S hS Z.obj X'.obj Q.obj z.hom x'.hom)

/-- **The morphism `Res_{Z_U/U}(W) ⟶ Mor_Q(Z, X')` of the fibre data of a pair.** A section of
`W_T → (Z_U)_T` over `T/U` is a pair of `Mor_Q(Z, X')` over `T`, by
`AlgebraicGeometry.Space.RelativeMorphism.ofFibrePair`, compatibly with base change. -/
noncomputable def relativeHomFibreMap (g : X' ⟶ X) (hg : g.hom ≫ x.hom = x'.hom)
    (p : RelativeMorphism B S hS Z.obj X.obj Q.obj z.hom x.hom (yoneda.obj U)) :
    (p.fibreSections g).presheaf ⟶ HX'.functor :=
  relativeHomOfPairs HX' (fun T v => p.ofFibrePair g hg ((p.fibreSections g).pairEquiv T.unop v))
    (p.ofFibrePair_natural g hg)

/-- The pair of `Mor_Q(Z, X')` that `AlgebraicGeometry.Space.relativeHomFibreMap` attaches to a
section. -/
@[simp]
theorem sections_relativeHomFibreMap (g : X' ⟶ X) (hg : g.hom ≫ x.hom = x'.hom)
    (p : RelativeMorphism B S hS Z.obj X.obj Q.obj z.hom x.hom (yoneda.obj U))
    (T : (BigFppfOver B S hS)ᵒᵖ) (v : (p.fibreSections g).presheaf.obj T) :
    HX'.sections T.unop ((relativeHomFibreMap HX' g hg p).app T v) =
      p.ofFibrePair g hg ((p.fibreSections g).pairEquiv T.unop v) :=
  sections_relativeHomOfPairs HX' _ (p.ofFibrePair_natural g hg) T v

/-- **Postcomposing the pair of a section of `Res_{Z_U/U}(W)` with `g` gives the base change of the
given pair.** -/
theorem RelativeMorphism.postcomp_ofFibrePair (g : X' ⟶ X) (hg : g.hom ≫ x.hom = x'.hom)
    (p : RelativeMorphism B S hS Z.obj X.obj Q.obj z.hom x.hom (yoneda.obj U))
    {T : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (q : RestrictionPair B S hS (p.fibreTotalMap g) p.fibreBaseMap T) :
    RelativeMorphism.postcomp g.hom hg (p.ofFibrePair g hg q) =
      RelativeMorphism.restrict q.base p := by
  have h1 : q.lift ≫ pullback.fst p.morphism g.hom =
      pullback.snd q.base (pullback.fst p.base z.hom) := q.over
  have key : ((pullbackBaseChangeIso p.base z.hom q.base).inv ≫
        q.lift ≫ pullback.snd p.morphism g.hom) ≫ g.hom =
      pullback.map (q.base ≫ p.base) z.hom p.base z.hom q.base (𝟙 Z.obj) (𝟙 Q.obj)
          (by simp) (by simp) ≫ p.morphism := by
    rw [Category.assoc, Category.assoc, ← pullback.condition, ← Category.assoc q.lift, h1,
      snd_eq_pullbackBaseChangeIso_hom_map p.base z.hom q.base, Category.assoc,
      Iso.inv_hom_id_assoc]
  exact RelativeMorphism.eq_restrict_of_comparison (f := q.base) rfl
    ⟨_, by simp, by simp, key⟩

variable (HX : RelativeHomConstruction B S hS Z.obj X.obj Q.obj z.hom x.hom)

/-- **The square of the fibre data commutes.** The projection of `Res_{Z_U/U}(W)` to `U`
followed by the given point of `Mor_Q(Z, X)` is `AlgebraicGeometry.Space.relativeHomFibreMap`
followed by the postcomposition morphism of `g`. -/
theorem relativeHomFibreMap_comp (g : X' ⟶ X) (hg : g.hom ≫ x.hom = x'.hom)
    (p : RelativeMorphism B S hS Z.obj X.obj Q.obj z.hom x.hom (yoneda.obj U)) :
    (p.fibreSections g).projection ≫ relativeHomPoint HX p =
      relativeHomFibreMap HX' g hg p ≫ relativeHomPostcompose HX' HX g.hom hg := by
  ext T v
  refine (HX.sections T.unop).injective ?_
  show HX.sections T.unop
      ((relativeHomPoint HX p).app T ((p.fibreSections g).projection.app T v)) =
    HX.sections T.unop ((relativeHomPostcompose HX' HX g.hom hg).app T
      ((relativeHomFibreMap HX' g hg p).app T v))
  have hl : HX.sections T.unop
      ((relativeHomPoint HX p).app T ((p.fibreSections g).projection.app T v)) =
        RelativeMorphism.restrict ((p.fibreSections g).pairEquiv T.unop v).base p := by
    rw [(p.fibreSections g).projection_pairEquiv T.unop v,
      HX.sections_app (relativeHomPoint HX p)
        (yonedaEquiv (((p.fibreSections g).pairEquiv T.unop v).base)),
      yoneda_map_yonedaEquiv, sections_relativeHomPoint]
  rw [hl, sections_relativeHomPostcompose, sections_relativeHomFibreMap,
    RelativeMorphism.postcomp_ofFibrePair]

/-! ### The fibre is the functor of sections -/

/-- **The first components of a lifted pair and of the base change agree.** -/
theorem RelativeMorphism.base_eq_of_postcomp_eq (g : X' ⟶ X) (hg : g.hom ≫ x.hom = x'.hom)
    (p : RelativeMorphism B S hS Z.obj X.obj Q.obj z.hom x.hom (yoneda.obj U))
    {T : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (c : T ⟶ yoneda.obj U)
    (r : RelativeMorphism B S hS Z.obj X'.obj Q.obj z.hom x'.hom T)
    (h : RelativeMorphism.postcomp g.hom hg r = RelativeMorphism.restrict c p) :
    r.base = c ≫ p.base :=
  congrArg RelativeMorphism.base h

/-- **The second components of a lifted pair and of the base change agree**, after the canonical
identification of the two fibre products. -/
theorem RelativeMorphism.morphism_comp_eq_of_postcomp_eq (g : X' ⟶ X)
    (hg : g.hom ≫ x.hom = x'.hom)
    (p : RelativeMorphism B S hS Z.obj X.obj Q.obj z.hom x.hom (yoneda.obj U))
    {T : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (c : T ⟶ yoneda.obj U)
    (r : RelativeMorphism B S hS Z.obj X'.obj Q.obj z.hom x'.hom T)
    (h : RelativeMorphism.postcomp g.hom hg r = RelativeMorphism.restrict c p) :
    r.morphism ≫ g.hom =
      (pullback.congrHom (p.base_eq_of_postcomp_eq g hg c r h) rfl).hom ≫
        pullback.map (c ≫ p.base) z.hom p.base z.hom c (𝟙 Z.obj) (𝟙 Q.obj) (by simp) (by simp) ≫
          p.morphism :=
  RelativeMorphism.morphism_eq_of_eq h (p.base_eq_of_postcomp_eq g hg c r h)

/-- **The two components of `AlgebraicGeometry.Space.RelativeMorphism.toFibrePair` land in the
fibre product `W = Z_U ×_{b, X} X'`.** The second component of the lifted pair postcomposed with
`g` is the second component of the base change of `(a, b)`, which is the projection to `Z_U` read
through `CategoryTheory.Limits.pullbackBaseChangeIso`. -/
theorem RelativeMorphism.toFibrePair_condition (g : X' ⟶ X) (hg : g.hom ≫ x.hom = x'.hom)
    (p : RelativeMorphism B S hS Z.obj X.obj Q.obj z.hom x.hom (yoneda.obj U))
    {T : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (c : T ⟶ yoneda.obj U)
    (r : RelativeMorphism B S hS Z.obj X'.obj Q.obj z.hom x'.hom T)
    (h : RelativeMorphism.postcomp g.hom hg r = RelativeMorphism.restrict c p) :
    pullback.snd c (pullback.fst p.base z.hom) ≫ p.morphism =
      ((pullbackBaseChangeIso p.base z.hom c).hom ≫
        (pullback.congrHom (p.base_eq_of_postcomp_eq g hg c r h) rfl).inv ≫ r.morphism) ≫
          g.hom := by
  rw [Category.assoc, Category.assoc, p.morphism_comp_eq_of_postcomp_eq g hg c r h,
    Iso.inv_hom_id_assoc, snd_eq_pullbackBaseChangeIso_hom_map p.base z.hom c, Category.assoc]

/-- **A pair of `Mor_Q(Z, X')` lifting the base change of the given pair is a section of
`W_T → (Z_U)_T`.** The section is the pair consisting of the projection to `(Z_U)_T` and the
second component of the lifted pair. -/
noncomputable abbrev RelativeMorphism.toFibrePair (g : X' ⟶ X) (hg : g.hom ≫ x.hom = x'.hom)
    (p : RelativeMorphism B S hS Z.obj X.obj Q.obj z.hom x.hom (yoneda.obj U))
    {T : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (c : T ⟶ yoneda.obj U)
    (r : RelativeMorphism B S hS Z.obj X'.obj Q.obj z.hom x'.hom T)
    (h : RelativeMorphism.postcomp g.hom hg r = RelativeMorphism.restrict c p) :
    RestrictionPair B S hS (p.fibreTotalMap g) p.fibreBaseMap T where
  base := c
  lift :=
    pullback.lift (pullback.snd c (pullback.fst p.base z.hom))
      ((pullbackBaseChangeIso p.base z.hom c).hom ≫
        (pullback.congrHom (p.base_eq_of_postcomp_eq g hg c r h) rfl).inv ≫ r.morphism)
      (p.toFibrePair_condition g hg c r h)
  over := pullback.lift_fst _ _ _

/-- The first component of `AlgebraicGeometry.Space.RelativeMorphism.toFibrePair`. -/
@[simp]
theorem RelativeMorphism.toFibrePair_base (g : X' ⟶ X) (hg : g.hom ≫ x.hom = x'.hom)
    (p : RelativeMorphism B S hS Z.obj X.obj Q.obj z.hom x.hom (yoneda.obj U))
    {T : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (c : T ⟶ yoneda.obj U)
    (r : RelativeMorphism B S hS Z.obj X'.obj Q.obj z.hom x'.hom T)
    (h : RelativeMorphism.postcomp g.hom hg r = RelativeMorphism.restrict c p) :
    (p.toFibrePair g hg c r h).base = c := rfl

/-- **`AlgebraicGeometry.Space.RelativeMorphism.toFibrePair` is a section of
`AlgebraicGeometry.Space.RelativeMorphism.ofFibrePair`.** -/
theorem RelativeMorphism.ofFibrePair_toFibrePair (g : X' ⟶ X) (hg : g.hom ≫ x.hom = x'.hom)
    (p : RelativeMorphism B S hS Z.obj X.obj Q.obj z.hom x.hom (yoneda.obj U))
    {T : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (c : T ⟶ yoneda.obj U)
    (r : RelativeMorphism B S hS Z.obj X'.obj Q.obj z.hom x'.hom T)
    (h : RelativeMorphism.postcomp g.hom hg r = RelativeMorphism.restrict c p) :
    r = p.ofFibrePair g hg (p.toFibrePair g hg c r h) := by
  refine RelativeMorphism.ext_of_base_eq (p.base_eq_of_postcomp_eq g hg c r h) ?_
  show r.morphism = (pullback.congrHom (p.base_eq_of_postcomp_eq g hg c r h) rfl).hom ≫
      (pullbackBaseChangeIso p.base z.hom c).inv ≫
        pullback.lift (pullback.snd c (pullback.fst p.base z.hom))
            ((pullbackBaseChangeIso p.base z.hom c).hom ≫
              (pullback.congrHom (p.base_eq_of_postcomp_eq g hg c r h) rfl).inv ≫ r.morphism)
            (p.toFibrePair_condition g hg c r h) ≫
          pullback.snd p.morphism g.hom
  rw [pullback.lift_snd, Iso.inv_hom_id_assoc, Iso.hom_inv_id_assoc]

/-- **`AlgebraicGeometry.Space.RelativeMorphism.toFibrePair` inverts
`AlgebraicGeometry.Space.RelativeMorphism.ofFibrePair`.** -/
theorem RelativeMorphism.toFibrePair_ofFibrePair (g : X' ⟶ X) (hg : g.hom ≫ x.hom = x'.hom)
    (p : RelativeMorphism B S hS Z.obj X.obj Q.obj z.hom x.hom (yoneda.obj U))
    {T : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (q : RestrictionPair B S hS (p.fibreTotalMap g) p.fibreBaseMap T) :
    p.toFibrePair g hg q.base (p.ofFibrePair g hg q) (p.postcomp_ofFibrePair g hg q) = q := by
  have hlift : (p.toFibrePair g hg q.base (p.ofFibrePair g hg q)
      (p.postcomp_ofFibrePair g hg q)).lift = q.lift := by
    refine pullback.hom_ext ((pullback.lift_fst _ _ _).trans q.over.symm) ?_
    rw [pullback.lift_snd, RelativeMorphism.ofFibrePair_morphism, pullback.congrHom_rfl_inv,
      Category.id_comp, Iso.hom_inv_id_assoc]
  exact RestrictionPair.ext_of_base_eq rfl
    (hlift.trans (by rw [pullback.congrHom_rfl, Category.id_comp]))

/-- **`AlgebraicGeometry.Space.RelativeMorphism.toFibrePair` depends only on its data.** -/
theorem RelativeMorphism.toFibrePair_congr (g : X' ⟶ X) (hg : g.hom ≫ x.hom = x'.hom)
    (p : RelativeMorphism B S hS Z.obj X.obj Q.obj z.hom x.hom (yoneda.obj U))
    {T : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {c c' : T ⟶ yoneda.obj U}
    {r r' : RelativeMorphism B S hS Z.obj X'.obj Q.obj z.hom x'.hom T}
    (h : RelativeMorphism.postcomp g.hom hg r = RelativeMorphism.restrict c p)
    (h' : RelativeMorphism.postcomp g.hom hg r' = RelativeMorphism.restrict c' p)
    (hc : c = c') (hr : r = r') :
    p.toFibrePair g hg c r h = p.toFibrePair g hg c' r' h' := by
  subst hc
  subst hr
  rfl

/-- **The comparison morphism from `Res_{Z_U/U}(W)` to the fibre product of `Mor_Q(Z, X')` and `U`
over `Mor_Q(Z, X)`.** -/
noncomputable def relativeHomFibreComparison (g : X' ⟶ X) (hg : g.hom ≫ x.hom = x'.hom)
    (p : RelativeMorphism B S hS Z.obj X.obj Q.obj z.hom x.hom (yoneda.obj U)) :
    (p.fibreSections g).presheaf ⟶
      pullback (relativeHomPoint HX p) (relativeHomPostcompose HX' HX g.hom hg) :=
  pullback.lift (p.fibreSections g).projection (relativeHomFibreMap HX' g hg p)
    (relativeHomFibreMap_comp HX' HX g hg p)

/-- The comparison morphism followed by the projection to `U`. -/
@[reassoc (attr := simp)]
theorem relativeHomFibreComparison_fst (g : X' ⟶ X) (hg : g.hom ≫ x.hom = x'.hom)
    (p : RelativeMorphism B S hS Z.obj X.obj Q.obj z.hom x.hom (yoneda.obj U)) :
    relativeHomFibreComparison HX' HX g hg p ≫
        pullback.fst (relativeHomPoint HX p) (relativeHomPostcompose HX' HX g.hom hg) =
      (p.fibreSections g).projection :=
  pullback.lift_fst _ _ _

/-- The comparison morphism followed by the projection to `Mor_Q(Z, X')`. -/
@[reassoc (attr := simp)]
theorem relativeHomFibreComparison_snd (g : X' ⟶ X) (hg : g.hom ≫ x.hom = x'.hom)
    (p : RelativeMorphism B S hS Z.obj X.obj Q.obj z.hom x.hom (yoneda.obj U)) :
    relativeHomFibreComparison HX' HX g hg p ≫
        pullback.snd (relativeHomPoint HX p) (relativeHomPostcompose HX' HX g.hom hg) =
      relativeHomFibreMap HX' g hg p :=
  pullback.lift_snd _ _ _

/-- **The comparison morphism is an isomorphism**: a section of `Res_{Z_U/U}(W)` over `T` is the
same thing as a morphism `T ⟶ U` together with a pair of `Mor_Q(Z, X')` over `T` lifting the base
change of `(a, b)`. This is the identification of the fibre of
`Mor_Q(Z, X') ⟶ Mor_Q(Z, X)` at a scheme-valued point with the functor of sections of
Stacks 05XR. -/
instance isIso_relativeHomFibreComparison (g : X' ⟶ X) (hg : g.hom ≫ x.hom = x'.hom)
    (p : RelativeMorphism B S hS Z.obj X.obj Q.obj z.hom x.hom (yoneda.obj U)) :
    IsIso (relativeHomFibreComparison HX' HX g hg p) := by
  have happ : ∀ T, IsIso ((relativeHomFibreComparison HX' HX g hg p).app T) := by
    intro T
    obtain ⟨T⟩ := T
    have hfst : ∀ v, (pullback.fst (relativeHomPoint HX p)
        (relativeHomPostcompose HX' HX g.hom hg)).app (op T)
          ((relativeHomFibreComparison HX' HX g hg p).app (op T) v) =
            (p.fibreSections g).projection.app (op T) v :=
      fun v => congrArg (fun k => (k.app (op T)) v)
        (relativeHomFibreComparison_fst HX' HX g hg p)
    have hsnd : ∀ v, (pullback.snd (relativeHomPoint HX p)
        (relativeHomPostcompose HX' HX g.hom hg)).app (op T)
          ((relativeHomFibreComparison HX' HX g hg p).app (op T) v) =
            (relativeHomFibreMap HX' g hg p).app (op T) v :=
      fun v => congrArg (fun k => (k.app (op T)) v)
        (relativeHomFibreComparison_snd HX' HX g hg p)
    rw [isIso_iff_bijective]
    refine ⟨fun v₁ v₂ hv => ?_, fun y => ?_⟩
    · refine ((p.fibreSections g).pairEquiv T).injective ?_
      have hb : ((p.fibreSections g).pairEquiv T v₁).base =
          ((p.fibreSections g).pairEquiv T v₂).base := by
        refine yonedaEquiv.injective ?_
        rw [← (p.fibreSections g).projection_pairEquiv T v₁,
          ← (p.fibreSections g).projection_pairEquiv T v₂, ← hfst v₁, ← hfst v₂, hv]
      have hr : p.ofFibrePair g hg ((p.fibreSections g).pairEquiv T v₁) =
          p.ofFibrePair g hg ((p.fibreSections g).pairEquiv T v₂) := by
        rw [← sections_relativeHomFibreMap HX' g hg p (op T) v₁,
          ← sections_relativeHomFibreMap HX' g hg p (op T) v₂, ← hsnd v₁, ← hsnd v₂, hv]
      refine (RelativeMorphism.toFibrePair_ofFibrePair g hg p
        ((p.fibreSections g).pairEquiv T v₁)).symm.trans ?_
      exact (RelativeMorphism.toFibrePair_congr g hg p _ _ hb hr).trans
        (RelativeMorphism.toFibrePair_ofFibrePair g hg p ((p.fibreSections g).pairEquiv T v₂))
    · have hc : (relativeHomPoint HX p).app (op T)
            ((pullback.fst (relativeHomPoint HX p)
              (relativeHomPostcompose HX' HX g.hom hg)).app (op T) y) =
          (relativeHomPostcompose HX' HX g.hom hg).app (op T)
            ((pullback.snd (relativeHomPoint HX p)
              (relativeHomPostcompose HX' HX g.hom hg)).app (op T) y) :=
        congrArg (fun k => (k.app (op T)) y)
          (pullback.condition (f := relativeHomPoint HX p)
            (g := relativeHomPostcompose HX' HX g.hom hg))
      have hpair : RelativeMorphism.postcomp g.hom hg
          (HX'.sections T ((pullback.snd (relativeHomPoint HX p)
            (relativeHomPostcompose HX' HX g.hom hg)).app (op T) y)) =
          RelativeMorphism.restrict
            (yoneda.map ((pullback.fst (relativeHomPoint HX p)
              (relativeHomPostcompose HX' HX g.hom hg)).app (op T) y)) p := by
        rw [← sections_relativeHomPostcompose HX' HX g.hom hg (op T) _, ← hc,
          HX.sections_app (relativeHomPoint HX p) _, sections_relativeHomPoint]
      refine ⟨((p.fibreSections g).pairEquiv T).symm (p.toFibrePair g hg _ _ hpair), ?_⟩
      refine pullbackObj_ext (relativeHomPoint HX p)
        (relativeHomPostcompose HX' HX g.hom hg) _ y ?_ ?_
      · rw [hfst, (p.fibreSections g).projection_pairEquiv, Equiv.apply_symm_apply,
          RelativeMorphism.toFibrePair_base, yonedaEquiv_yoneda_map]
      · rw [hsnd]
        refine (HX'.sections T).injective ?_
        rw [sections_relativeHomFibreMap, Equiv.apply_symm_apply]
        exact (RelativeMorphism.ofFibrePair_toFibrePair g hg p _ _ hpair).symm
  exact NatIso.isIso_of_isIso_app _

/-- **The fibre of `Mor_Q(Z, X') ⟶ Mor_Q(Z, X)` at a scheme-valued point is `Res_{Z_U/U}(W)`,** the
functor of sections of `W ⟶ Z_U` over `U` of Stacks 05XR. -/
noncomputable def relativeHomFibreIso (g : X' ⟶ X) (hg : g.hom ≫ x.hom = x'.hom)
    (p : RelativeMorphism B S hS Z.obj X.obj Q.obj z.hom x.hom (yoneda.obj U)) :
    (p.fibreSections g).presheaf ≅
      pullback (relativeHomPoint HX p) (relativeHomPostcompose HX' HX g.hom hg) :=
  asIso (relativeHomFibreComparison HX' HX g hg p)

end Fibre

/-! ### Stacks 05Y5 -/

section Main

variable {X' X Z Q : AlgebraicSpaces B S hS} {x' : X' ⟶ Q} {x : X ⟶ Q} {z : Z ⟶ Q}
  (HX' : RelativeHomConstruction B S hS Z.obj X'.obj Q.obj z.hom x'.hom)
  (HX : RelativeHomConstruction B S hS Z.obj X.obj Q.obj z.hom x.hom)
  (g : X' ⟶ X) (hg : g.hom ≫ x.hom = x'.hom)

/-- The fibre data of a pair over a scheme instantiates
`AlgebraicGeometry.Space.IsFibreSectionsAlgebraicEtale`: `Z_U` is the base change of `z` along the
first component and `W` is the fibre product of `g` over the second. -/
theorem relativeHomFibreSections_algebraic_etale
    (h05XR : IsFibreSectionsAlgebraicEtale B S hS g z) (hg_etale : IsEtale B S hS g.hom)
    (hz : IsFiniteLocallyFree B S hS z) {U : BigFppfOver B S hS}
    (p : RelativeMorphism B S hS Z.obj X.obj Q.obj z.hom x.hom (yoneda.obj U)) :
    IsAlgebraicSpace B S hS (p.fibreSections g).presheaf ∧
      IsEtale B S hS (p.fibreSections g).projection :=
  h05XR hg_etale hz U p.fibreBase (p.fibreTotal g) p.fibreBaseMap (p.fibreTotalMap g) p.base
    (pullback.snd p.base z.hom) p.morphism (pullback.snd p.morphism g.hom)
    (IsPullback.of_hasPullback p.base z.hom) (IsPullback.of_hasPullback p.morphism g.hom)

/-- The fibre data of a pair over a scheme instantiates
`AlgebraicGeometry.Space.IsFibreSectionsSurjective`. -/
theorem relativeHomFibreSections_surjective (h05XQ : IsFibreSectionsSurjective B S hS g z)
    (hg_etale : IsEtale B S hS g.hom) (hg_surjective : IsSurjective B S hS g.hom)
    (hz : IsFiniteLocallyFree B S hS z) {U : BigFppfOver B S hS}
    (p : RelativeMorphism B S hS Z.obj X.obj Q.obj z.hom x.hom (yoneda.obj U)) :
    IsSurjective B S hS (p.fibreSections g).projection :=
  h05XQ hg_etale hg_surjective hz U p.fibreBase (p.fibreTotal g) p.fibreBaseMap
    (p.fibreTotalMap g) p.base (pullback.snd p.base z.hom) p.morphism
    (pullback.snd p.morphism g.hom) (IsPullback.of_hasPullback p.base z.hom)
    (IsPullback.of_hasPullback p.morphism g.hom)

/-- **Stacks 05Y5, first conclusion.** Let `S` be a scheme, let `Z → B` and `X' → X → B` be
morphisms of algebraic spaces over `S` with `X' → X` étale and `Z → B` finite locally free. Then
`Mor_B(Z, X') → Mor_B(Z, X)` is representable by algebraic spaces, provided
`AlgebraicGeometry.Space.IsFibreSectionsAlgebraicEtale` holds for `g` and `z`. -/
theorem isRepresentableByAlgebraicSpaces_relativeHomPostcompose
    (hg_etale : IsEtale B S hS g.hom) (hz : IsFiniteLocallyFree B S hS z)
    (h05XR : IsFibreSectionsAlgebraicEtale B S hS g z) :
    IsRepresentableByAlgebraicSpaces B S hS (relativeHomPostcompose HX' HX g.hom hg) := by
  intro U ξ
  rw [← relativeHomPoint_sections HX ξ]
  exact (relativeHomFibreSections_algebraic_etale g h05XR hg_etale hz
      (HX.sections U (yonedaEquiv ξ))).1.of_iso
    (relativeHomFibreIso HX' HX g hg (HX.sections U (yonedaEquiv ξ)))

/-- **Stacks 05Y5, second conclusion.** In the situation of
`AlgebraicGeometry.Space.isRepresentableByAlgebraicSpaces_relativeHomPostcompose`, the morphism
`Mor_B(Z, X') → Mor_B(Z, X)` is étale: every base change of it along a scheme-valued point of its
target is an étale morphism of algebraic spaces. -/
theorem hasProperty_isEtale_relativeHomPostcompose
    (hg_etale : IsEtale B S hS g.hom) (hz : IsFiniteLocallyFree B S hS z)
    (h05XR : IsFibreSectionsAlgebraicEtale B S hS g z) :
    HasProperty B S hS (fun _ _ f => IsEtale B S hS f.hom)
      (relativeHomPostcompose HX' HX g.hom hg)
      (isRepresentableByAlgebraicSpaces_relativeHomPostcompose HX' HX g hg hg_etale hz h05XR) := by
  intro U ξ
  have he := (relativeHomFibreSections_algebraic_etale g h05XR hg_etale hz
    (HX.sections U (yonedaEquiv ξ))).2
  have hp : relativeHomPoint HX (HX.sections U (yonedaEquiv ξ)) = ξ :=
    relativeHomPoint_sections HX ξ
  show IsEtale B S hS (pullback.fst ξ (relativeHomPostcompose HX' HX g.hom hg))
  rw [← hp]
  refine IsEtale.of_iso_comp
    (relativeHomFibreIso HX' HX g hg (HX.sections U (yonedaEquiv ξ))) ?_
  rw [relativeHomFibreIso, asIso_hom, relativeHomFibreComparison_fst]
  exact he

/-- **Stacks 05Y5, third conclusion.** If `X' → X` is in addition surjective then
`Mor_B(Z, X') → Mor_B(Z, X)` is surjective, provided
`AlgebraicGeometry.Space.IsFibreSectionsSurjective` holds for `g` and `z`. -/
theorem isSurjective_relativeHomPostcompose (hg_etale : IsEtale B S hS g.hom)
    (hg_surjective : IsSurjective B S hS g.hom) (hz : IsFiniteLocallyFree B S hS z)
    (h05XQ : IsFibreSectionsSurjective B S hS g z) :
    IsSurjective B S hS (relativeHomPostcompose HX' HX g.hom hg) := by
  intro P
  induction P using Quot.ind with
  | _ p₀ =>
    set U := p₀.siteObject with hU
    set ξ : yoneda.obj U ⟶ HX.functor := yonedaEquiv.symm p₀.value with hξ
    set p := HX.sections U (yonedaEquiv ξ) with hpdef
    have hp : relativeHomPoint HX p = ξ := relativeHomPoint_sections HX ξ
    have hsp := relativeHomFibreSections_surjective g h05XQ hg_etale hg_surjective hz p
    let e : FieldValuedPoint B S hS (yoneda.obj U) :=
      { carrier := p₀.carrier
        field := p₀.field
        contained := p₀.contained
        toBase := p₀.toBase
        value := 𝟙 U }
    obtain ⟨ρ, hρ⟩ := hsp (e.class B S hS (yoneda.obj U))
    refine ⟨pointsMap B S hS (p.fibreSections g).presheaf
      (relativeHomFibreMap HX' g hg p) ρ, ?_⟩
    have hval : ξ.app (op U) (𝟙 U) = p₀.value := Equiv.apply_symm_apply yonedaEquiv p₀.value
    have hcls : (FieldValuedPoint.map B S hS (yoneda.obj U) ξ e).class B S hS HX.functor =
        p₀.class B S hS HX.functor := by
      refine Quot.sound ⟨p₀, ⟨𝟙 U, ?_⟩,
        FieldValuedPoint.dominates_refl B S hS HX.functor p₀⟩
      show HX.functor.map (𝟙 (op U))
        ((FieldValuedPoint.map B S hS (yoneda.obj U) ξ e).value) = p₀.value
      rw [CategoryTheory.Functor.map_id]
      exact hval
    calc pointsMap B S hS HX'.functor (relativeHomPostcompose HX' HX g.hom hg)
            (pointsMap B S hS (p.fibreSections g).presheaf
              (relativeHomFibreMap HX' g hg p) ρ)
        = pointsMap B S hS (p.fibreSections g).presheaf
            (relativeHomFibreMap HX' g hg p ≫ relativeHomPostcompose HX' HX g.hom hg) ρ :=
          (congrFun (pointsMap_comp B S hS (p.fibreSections g).presheaf
            (relativeHomFibreMap HX' g hg p) (relativeHomPostcompose HX' HX g.hom hg)) ρ).symm
      _ = pointsMap B S hS (p.fibreSections g).presheaf
            ((p.fibreSections g).projection ≫ relativeHomPoint HX p) ρ := by
          rw [relativeHomFibreMap_comp HX' HX g hg p]
      _ = pointsMap B S hS (yoneda.obj U) (relativeHomPoint HX p)
            (pointsMap B S hS (p.fibreSections g).presheaf
              (p.fibreSections g).projection ρ) :=
          congrFun (pointsMap_comp B S hS (p.fibreSections g).presheaf
            (p.fibreSections g).projection (relativeHomPoint HX p)) ρ
      _ = pointsMap B S hS (yoneda.obj U) ξ (e.class B S hS (yoneda.obj U)) := by
          rw [hρ, hp]
      _ = p₀.class B S hS HX.functor := hcls

end Main

end AlgebraicGeometry.Space

end
