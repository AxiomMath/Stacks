module

public import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
public import Mathlib.AlgebraicGeometry.Sites.Representability
public import Mathlib.CategoryTheory.Limits.Constructions.Over.Products
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Shapes.Pullbacks
public import Mathlib.CategoryTheory.Limits.Types.Pullbacks
public import Mathlib.CategoryTheory.Sites.EqualizerSheafCondition
public import StacksFrontier.AlgebraicGeometry.Morphisms.Affine.QuasiAffineQuasiFinite
public import StacksFrontier.AlgebraicGeometry.Morphisms.FiniteLocallyFree.FreeOnAffineOpen
public import StacksFrontier.AlgebraicGeometry.Morphisms.WeaklyEtale.RelativeMorphisms
public import StacksFrontier.AlgebraicGeometry.Topologies.FpqcQuasicoherentReduction
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Representability of morphisms out of a finite locally free scheme

Let `Z` and `X` be schemes over `S` with `Z ⟶ S` finite locally free. If every finite set of
points of `X` lying in one fibre of `X ⟶ S` is contained in an affine open of `X`, then the
functor of `S`-morphisms from `Z` to `X` is representable by a scheme.

## Main results

* `Stacks.Morphisms.homFromFiniteLocallyFree_isRepresentable` is Stacks Tag 0BL4.
* `Stacks.Morphisms.relativeHom_isRepresentable_of_locallyQuasiFinite` is Stacks Tag 0BL5: the
  hypothesis of Tag 0BL4 holds when `X ⟶ S` is separated and quasi-finite.

## Implementation notes

The relative morphism functor is written on the slice over `S`: it sends an `S`-scheme `T` to the
`S`-morphisms from `T ⨯ₛ Z` to `X`, that is, it is the Yoneda functor of `X` precomposed with the
opposite of the product-with-`Z` functor. Representability is established on the base category
rather than on the slice, by passing to the total presheaf `Stacks.Sites.totalPresheaf` — the
presheaf `T ↦ Σ a : T ⟶ S, Mor_S(T ⨯ₛ Z, X)` on all schemes. Being a sheaf over the slice and
being a sheaf on the base are equivalent there
(`Stacks.Sites.isSheaf_over_iff_isSheaf_totalPresheaf`), and representability transfers both ways
(`Stacks.Morphisms.totalRepresentableBy` and
`Stacks.Morphisms.representable_of_totalRepresentable`). Mathlib's
`AlgebraicGeometry.Scheme.LocalRepresentability.isRepresentable` (Stacks Tag 01JJ) then glues a
family of open immersions of representable presheaves into the total presheaf.

The charts are indexed by `Stacks.Morphisms.AffineChartIndex`: an affine open `V` of `S` over
which the base change of `Z` has *finite free* global sections, together with an affine open `U`
of `X` above `V`. Over such a chart the relative morphism functor is represented by an affine
scheme, which is Stacks Tag 05Y6 in the form
`AlgebraicGeometry.relativeHom_representableBy_affine`; the freeness field of the index is what
`Stacks.Morphisms.exists_isAffineOpen_module_finite_and_free` supplies, and it is the reason the
index records an affine open of `S` of a restricted kind rather than an arbitrary one.

That the charts cover is the geometric content: for a point `t` of a test scheme `T` carrying a
morphism `a : T ⟶ S` and an `S`-morphism `b : T ⨯ₛ Z ⟶ X`, the image under `b` of the fibre of
`T ⨯ₛ Z` over `t` is a *finite* set of points of `X` in one fibre over `a t`, because a finite
locally free morphism is finite and its base changes have finite fibres. The hypothesis of the
theorem then puts that finite set inside an affine open, which is shrunk into `g ⁻¹ᵁ V` by
`Stacks.Morphisms.exists_affineOpen_between`. The locus of points of `T` where this works is open
because `T ⨯ₛ Z ⟶ T` is universally closed, which is `Stacks.Morphisms.goodOpen`.

## References

* [Stacks Project, Tag 0BL4](https://stacks.math.columbia.edu/tag/0BL4)
* [Stacks Project, Tag 0BL5](https://stacks.math.columbia.edu/tag/0BL5)
* [Stacks Project, Tag 07S0](https://stacks.math.columbia.edu/tag/07S0)
* [Stacks Project, Tag 05Y6](https://stacks.math.columbia.edu/tag/05Y6)
* [Stacks Project, Tag 01JJ](https://stacks.math.columbia.edu/tag/01JJ)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite Cardinal
open Stacks.Sites (totalPresheaf)

universe u

namespace Stacks.Morphisms

/-! ### Consequences of finite local freeness used by the covering argument -/

/-- A finite locally free morphism is universally closed, being finite. -/
private theorem universallyClosed_of_isFiniteLocallyFree {Z S : Scheme.{u}} (f : Z ⟶ S)
    [IsFiniteLocallyFree f] : UniversallyClosed f := by
  let : IsFinite f := IsFiniteLocallyFree.isFinite f
  infer_instance

/-- A base change of a finite locally free morphism, in the shape used below. Finite local
freeness is stable under base change, but the stability instance is not found by instance
search, so it is fed as a term. -/
private theorem isFiniteLocallyFree_pullback_fst {T Z S : Scheme.{u}} (f : Z ⟶ S)
    [IsFiniteLocallyFree f] (a : T ⟶ S) : IsFiniteLocallyFree (pullback.fst a f) := by
  have hbc : MorphismProperty.IsStableUnderBaseChange
      (@IsFiniteLocallyFree : MorphismProperty Scheme.{u}) :=
    isFiniteLocallyFree_isStableUnderBaseChange
  exact hbc.of_isPullback (IsPullback.of_hasPullback a f).flip ‹IsFiniteLocallyFree f›

/-- The fibres of a base change of a finite locally free morphism are finite: such a morphism is
finite, hence locally quasi-finite and quasi-compact. -/
private theorem finite_fiber_pullback {T Z S : Scheme.{u}} (f : Z ⟶ S)
    [IsFiniteLocallyFree f] (a : T ⟶ S) (t : T) :
    ((pullback.fst a f).base ⁻¹' {t}).Finite := by
  let : IsFiniteLocallyFree (pullback.fst a f) := isFiniteLocallyFree_pullback_fst f a
  let : IsFinite (pullback.fst a f) := IsFiniteLocallyFree.isFinite _
  let : LocallyQuasiFinite (pullback.fst a f) := inferInstance
  let : QuasiCompact (pullback.fst a f) := inferInstance
  exact (pullback.fst a f).finite_preimage_singleton t

/-- A base change of a finite locally free morphism is universally closed. -/
private theorem universallyClosed_pullback {T Z S : Scheme.{u}} (f : Z ⟶ S)
    [IsFiniteLocallyFree f] (a : T ⟶ S) : UniversallyClosed (pullback.fst a f) :=
  let _ : IsFiniteLocallyFree (pullback.fst a f) := isFiniteLocallyFree_pullback_fst f a
  universallyClosed_of_isFiniteLocallyFree _

/-! ### The open locus of a chart -/

/-- The open set of points `t` of `T` lying over `V` and all of whose fibre in `Y` is carried
into `U`. It is open because the complement of `U` is closed and `p` is universally closed, hence
a closed map. -/
private def goodOpen {T Y S X : Scheme.{u}} (a : T ⟶ S) (p : Y ⟶ T) (b : Y ⟶ X)
    (V : S.Opens) (U : X.Opens) [UniversallyClosed p] : T.Opens :=
  ⟨(a.base ⁻¹' (V : Set S)) \ p.base '' (b.base ⁻¹' (U : Set X)ᶜ),
    (V.2.preimage a.continuous).sdiff (p.isClosedMap _ (U.2.isClosed_compl.preimage b.continuous))⟩

/-- Membership in `Stacks.Morphisms.goodOpen`, spelled out. -/
private lemma mem_goodOpen {T Y S X : Scheme.{u}} (a : T ⟶ S) (p : Y ⟶ T) (b : Y ⟶ X)
    (V : S.Opens) (U : X.Opens) [UniversallyClosed p] (t : T) :
    t ∈ goodOpen a p b V U ↔
      a.base t ∈ V ∧ ∀ y : Y, p.base y = t → b.base y ∈ U := by
  show (t ∈ a.base ⁻¹' (V : Set S) ∧
      t ∉ p.base '' (b.base ⁻¹' (U : Set X)ᶜ)) ↔ _
  exact and_congr_right fun _ ↦ ⟨fun hnot y hxy ↦ Classical.byContradiction fun hy ↦
    hnot ⟨y, hy, hxy⟩, fun hall ⟨y, hy, hxy⟩ ↦ hy (hall y hxy)⟩

/-! ### Elementary calculus in the total presheaf -/

/-- Two elements of the total presheaf built from restrictions of one section along two
morphisms of the slice with the same underlying morphism of schemes agree. -/
private lemma totalSigmaMkEq {S : Scheme.{u}} {F : (Over S)ᵒᵖ ⥤ Type u}
    {V W : Scheme.{u}} {φ : W ⟶ S} (s : F.obj (op (Over.mk φ)))
    {ψ ψ' : V ⟶ S} (e : Over.mk ψ ⟶ Over.mk φ) (e' : Over.mk ψ' ⟶ Over.mk φ)
    (h : e.left = e'.left) :
    (⟨ψ, F.map e.op s⟩ : Σ χ : V ⟶ S, F.obj (op (Over.mk χ))) = ⟨ψ', F.map e'.op s⟩ := by
  have h1 := Over.w e
  have h2 := Over.w e'
  simp only [Over.mk_hom, Over.mk_left] at h1 h2
  have hψ : ψ = ψ' := by rw [← h1, ← h2, h]
  subst hψ
  rw [Over.OverMorphism.ext h]

/-- The section of `F` at `A` carried by an element of the total presheaf whose first component
is the structure morphism of `A`. -/
private def totalSection {S : Scheme.{u}} {F : (Over S)ᵒᵖ ⥤ Type u}
    {A : Over S} (p : (totalPresheaf F).obj (op A.left))
    (h : p.1 = A.hom) : F.obj (op A) :=
  F.map (Over.homMk (𝟙 A.left) (by simpa using h) : A ⟶ Over.mk p.1).op p.2

/-- The first component of a restriction of an element of the total presheaf whose first
component is a structure morphism is again a structure morphism. -/
private lemma totalMapFst {S : Scheme.{u}} {F : (Over S)ᵒᵖ ⥤ Type u}
    {A B : Over S} (b : B ⟶ A) {p : (totalPresheaf F).obj (op A.left)}
    (h : p.1 = A.hom) {q : (totalPresheaf F).obj (op B.left)}
    (hq : (totalPresheaf F).map b.left.op p = q) : q.1 = B.hom := by
  subst hq
  show b.left ≫ p.1 = B.hom
  rw [h]
  exact Over.w b

/-- `Stacks.Morphisms.totalSection` recovers the element of the total presheaf it came from. -/
private lemma totalMkSection {S : Scheme.{u}} {F : (Over S)ᵒᵖ ⥤ Type u}
    {A : Over S} (p : (totalPresheaf F).obj (op A.left)) (h : p.1 = A.hom) :
    (⟨A.hom, totalSection p h⟩ : (totalPresheaf F).obj (op A.left)) = p := by
  have h1 := totalSigmaMkEq p.2
    (Over.homMk (𝟙 A.left) (by simpa using h) : Over.mk A.hom ⟶ Over.mk p.1)
    (𝟙 (Over.mk p.1)) (by simp)
  have h2 : (⟨p.1, F.map (𝟙 (Over.mk p.1)).op p.2⟩ :
      (totalPresheaf F).obj (op A.left)) = p := by
    cases p
    simp
  exact h1.trans h2

/-- Restriction in the total presheaf of an element assembled from a section of `F`. -/
private lemma totalMapMk {S : Scheme.{u}} {F : (Over S)ᵒᵖ ⥤ Type u}
    {A B : Over S} (b : B ⟶ A) (t : F.obj (op A)) :
    (totalPresheaf F).map b.left.op (⟨A.hom, t⟩ : (totalPresheaf F).obj (op A.left)) =
      ⟨B.hom, F.map b.op t⟩ := by
  show (⟨b.left ≫ A.hom,
    F.map (Over.homMk b.left rfl : Over.mk (b.left ≫ A.hom) ⟶ Over.mk A.hom).op t⟩ :
      (totalPresheaf F).obj (op B.left)) = ⟨B.hom, F.map b.op t⟩
  exact totalSigmaMkEq t
    (Over.homMk b.left rfl : Over.mk (b.left ≫ A.hom) ⟶ Over.mk A.hom) b rfl

/-- Two elements of the total presheaf with the same first component agree as soon as their
second components do. -/
private lemma totalSigmaSndInj {S : Scheme.{u}} {F : (Over S)ᵒᵖ ⥤ Type u}
    {V : Scheme.{u}} {φ : V ⟶ S} {s t : F.obj (op (Over.mk φ))}
    (hst : (⟨φ, s⟩ : Σ ψ : V ⟶ S, F.obj (op (Over.mk ψ))) = ⟨φ, t⟩) : s = t := by
  simpa using hst

/-- `Stacks.Morphisms.totalSection` commutes with restriction. -/
private lemma totalMapSection {S : Scheme.{u}} {F : (Over S)ᵒᵖ ⥤ Type u}
    {A B : Over S} (b : B ⟶ A) {p : (totalPresheaf F).obj (op A.left)}
    (h : p.1 = A.hom) {q : (totalPresheaf F).obj (op B.left)}
    (hq : (totalPresheaf F).map b.left.op p = q) :
    F.map b.op (totalSection p h) = totalSection q (totalMapFst b h hq) :=
  totalSigmaSndInj <| (totalMapMk b (totalSection p h)).symm.trans <|
    ((congrArg (fun s => (totalPresheaf F).map b.left.op s) (totalMkSection p h)).trans hq).trans
      (totalMkSection q (totalMapFst b h hq)).symm

/-- The total presheaf of an isomorphic presheaf on the slice. -/
private def totalIso {S : Scheme.{u}} {F G : (Over S)ᵒᵖ ⥤ Type u} (e : F ≅ G) :
    totalPresheaf F ≅ totalPresheaf G :=
  NatIso.ofComponents (fun T ↦ (Equiv.sigmaCongrRight
    (fun a : T.unop ⟶ S ↦ (e.app (op (Over.mk a))).toEquiv)).toIso) (by
      intro T T' k
      apply ConcreteCategory.hom_ext
      rintro ⟨a, m⟩
      exact congrArg (fun n ↦ (⟨k.unop ≫ a, n⟩ : (totalPresheaf G).obj T'))
        (e.hom.naturality_apply _ m))

/-- The morphism of total presheaves attached to a morphism from a presheaf on the slice over `V`
to the restriction along `i` of a presheaf on the slice over `S`. -/
private def totalMap {S V : Scheme.{u}} (i : V ⟶ S)
    {F : (Over V)ᵒᵖ ⥤ Type u} {G : (Over S)ᵒᵖ ⥤ Type u}
    (η : F ⟶ (Over.map i).op ⋙ G) : totalPresheaf F ⟶ totalPresheaf G where
  app T := ↾ fun x ↦ ⟨x.1 ≫ i, η.app _ x.2⟩
  naturality {T T'} k := by
    apply ConcreteCategory.hom_ext
    rintro ⟨a, m⟩
    have hh := totalMapMk (F := F) (Over.homMk k.unop rfl :
      Over.mk (k.unop ≫ a) ⟶ Over.mk a) m
    have hg := totalMapMk (F := G) ((Over.map i).map (Over.homMk k.unop rfl :
      Over.mk (k.unop ≫ a) ⟶ Over.mk a)) (η.app _ m)
    change (totalPresheaf F).map k ⟨a, m⟩ =
      ⟨k.unop ≫ a, F.map (Over.homMk k.unop rfl :
        Over.mk (k.unop ≫ a) ⟶ Over.mk a).op m⟩ at hh
    change (totalPresheaf G).map k ⟨a ≫ i, η.app _ m⟩ =
      ⟨(k.unop ≫ a) ≫ i, G.map ((Over.map i).map (Over.homMk k.unop rfl :
        Over.mk (k.unop ≫ a) ⟶ Over.mk a)).op (η.app _ m)⟩ at hg
    symm
    change (totalPresheaf G).map k ⟨a ≫ i, η.app _ m⟩ =
      (fun x : (totalPresheaf F).obj T' ↦
        (⟨x.1 ≫ i, η.app _ x.2⟩ : (totalPresheaf G).obj T'))
        ((totalPresheaf F).map k ⟨a, m⟩)
    rw [hh, hg]
    exact congrArg (fun z ↦ (⟨(k.unop ≫ a) ≫ i, z⟩ :
      (totalPresheaf G).obj T'))
      (η.naturality_apply (Over.homMk k.unop rfl :
        Over.mk (k.unop ≫ a) ⟶ Over.mk a).op m).symm

/-! ### The relative morphism functor on the slice, and on the base -/

/-- **The product-with-`Z` functor on the slice over `S` is pullback followed by composition.**
The underlying scheme of `Z ⨯ A` in `CategoryTheory.Over S` is the fibre product of `A` and `Z`
over `S`, and its structure morphism is the one obtained by composing. -/
private def productPullbackIso {S Z : Scheme.{u}} (f : Z ⟶ S) :
    Limits.prod.functor.obj (Over.mk f) ≅
      Over.pullback (Over.mk f).hom ⋙ Over.map (Over.mk f).hom := by
  refine NatIso.ofComponents (fun A => ?_) ?_
  · have hprod : (Limits.prod.functor.obj (Over.mk f)).obj A =
      ((Over.mk f) ⨯ A) := rfl
    cases hprod
    let e : ((Over.mk f) ⨯ A).left ≅
        Limits.pullback A.hom f :=
      Over.prodLeftIsoPullback (Over.mk f) A ≪≫
        Limits.pullbackSymmetry f A.hom
    refine Over.isoMk e ?_
    change e.hom ≫ pullback.snd A.hom f ≫ f =
      ((Over.mk f) ⨯ A).hom
    calc
      e.hom ≫ pullback.snd A.hom f ≫ f =
          (Over.prodLeftIsoPullback (Over.mk f) A).hom ≫
            pullback.fst f A.hom ≫ f := by
        dsimp [e]
        simpa only [Category.assoc] using
          congrArg (fun k => ((Over.prodLeftIsoPullback (Over.mk f) A).hom ≫ k) ≫ f)
            (Limits.pullbackSymmetry_hom_comp_snd f A.hom)
      _ = (prod.fst (X := Over.mk f)).left ≫ f :=
        congrArg (fun (k : ((Over.mk f) ⨯ A).left ⟶ Z) => k ≫ f)
          (Over.prodLeftIsoPullback_hom_fst (Over.mk f) A)
      _ = ((Over.mk f) ⨯ A).hom :=
        Over.w (prod.fst (X := Over.mk f))
  · intro A B b
    apply Over.OverMorphism.ext
    change
      (prod.map (𝟙 (Over.mk f)) b).left ≫
          (Over.prodLeftIsoPullback (Over.mk f) B ≪≫ pullbackSymmetry f B.hom).hom =
        (Over.prodLeftIsoPullback (Over.mk f) A ≪≫ pullbackSymmetry f A.hom).hom ≫
          ((Over.pullback f).map b).left
    have hfst (Y : Over S) : (Over.prodLeftIsoPullback (Over.mk f) Y).hom ≫ pullback.fst f Y.hom =
        (prod.fst (X := Over.mk f)).left := Over.prodLeftIsoPullback_hom_fst _ _
    have hsnd (Y : Over S) : (Over.prodLeftIsoPullback (Over.mk f) Y).hom ≫ pullback.snd f Y.hom =
        (prod.snd (X := Over.mk f)).left := Over.prodLeftIsoPullback_hom_snd _ _
    apply pullback.hom_ext
    · simp only [Over.mk_left, Over.mk_hom, Iso.trans_hom, Category.assoc,
        pullbackSymmetry_hom_comp_fst, hsnd, ← Over.comp_left, prod.map_snd,
        Over.pullback_obj_left, Over.pullback_map_left]
      simp [pullback.lift_fst, reassoc_of% (hsnd A)]
    · simp only [Over.mk_left, Over.mk_hom, Iso.trans_hom, Category.assoc,
        pullbackSymmetry_hom_comp_snd, hfst, ← Over.comp_left, prod.map_fst, Category.comp_id,
        Over.pullback_obj_left, Over.pullback_map_left]
      simp [pullback.lift_snd, hfst]

/-- **The relative morphism functor is a Zariski sheaf on the slice.**  The product-with-`Z`
functor on the slice is `CategoryTheory.Over.star` followed by `CategoryTheory.Over.forget`, both
continuous for the localized Zariski topologies, and the Zariski topology is subcanonical. -/
@[sga "3 IV 6.1.1" "more general"]
private lemma relativeHom_isSheaf {S : Scheme.{u}} (Z X : Over S) :
    Presheaf.IsSheaf (Scheme.zariskiTopology.over S)
      ((prod.functor.obj Z).op ⋙ yoneda.obj X) := by
  let J := Scheme.zariskiTopology.over S
  have : (prod.functor.obj Z).IsContinuous J J := by
    show (Over.star Z ⋙ Over.forget Z).IsContinuous J J
    exact Functor.isContinuous_comp _ _ J (J.over Z) J
  apply Functor.op_comp_isSheaf_of_isSheaf _ J J
  exact (isSheaf_iff_isSheaf_of_type _ _).mpr
    (GrothendieckTopology.Subcanonical.isSheaf_of_isRepresentable _)

/-- The relative morphism functor from `Z` to `X` over `S`, written with the pullback form of the
product on the slice.  This is the shape in which the chart morphisms below are built. -/
private abbrev pullbackHom {S Z X : Scheme.{u}} (f : Z ⟶ S) (g : X ⟶ S) :=
  (Over.pullback f ⋙ Over.map f).op ⋙ yoneda.obj (Over.mk g)

/-- The two forms of the relative morphism functor agree. -/
private def pullbackHomIso {S Z X : Scheme.{u}} (f : Z ⟶ S) (g : X ⟶ S) :
    ((prod.functor.obj (Over.mk f)).op ⋙ yoneda.obj (Over.mk g)) ≅ pullbackHom f g :=
  (Functor.isoWhiskerRight (NatIso.op (productPullbackIso f))
    (yoneda.obj (Over.mk g))).symm

/-- **The total presheaf of the relative morphism functor is a Zariski sheaf on all schemes.**
This is `Stacks.Sites.isSheaf_over_iff_isSheaf_totalPresheaf` applied to
`Stacks.Morphisms.relativeHom_isSheaf`, the sheaf condition for `CategoryTheory.yoneda.obj S`
coming from subcanonicity of the Zariski topology. -/
@[sga "3 IV 6.1.1" "more general", sga "3 VIII 1.7.1"]
private lemma totalPullbackHom_isSheaf {S Z X : Scheme.{u}} (f : Z ⟶ S) (g : X ⟶ S) :
    Presieve.IsSheaf Scheme.zariskiTopology (totalPresheaf (pullbackHom f g)) := by
  let : Scheme.zariskiTopology.{u}.Subcanonical := Scheme.subcanonical_zariskiTopology
  have hy : Presieve.IsSheaf Scheme.zariskiTopology.{u} (yoneda.obj S) :=
    GrothendieckTopology.Subcanonical.isSheaf_of_isRepresentable _
  refine Presieve.isSheaf_iso _ (totalIso (pullbackHomIso f g)) ?_
  refine (Stacks.Sites.isSheaf_over_iff_isSheaf_totalPresheaf Scheme.zariskiTopology
    ((prod.functor.obj (Over.mk f)).op ⋙ yoneda.obj (Over.mk g)) hy).1 ?_
  exact (isSheaf_iff_isSheaf_of_type _ _).1 (relativeHom_isSheaf (Over.mk f) (Over.mk g))

/-! ### Transfer of representability, and the charts -/

/-- **Representability of the total presheaf implies representability of the presheaf on the
slice.**  The representing object of the slice presheaf is the representing scheme of the total
presheaf, equipped with the first component of the universal element as its structure
morphism. -/
private def representableByOfTotalRepresentable {S : Scheme.{u}}
    {F : (Over S)ᵒᵖ ⥤ Type u} {W : Scheme.{u}}
    (R : (totalPresheaf F).RepresentableBy W) :
    F.RepresentableBy (Over.mk (R.homEquiv (𝟙 W)).1) := by
  let x := R.homEquiv (𝟙 W)
  let φ : W ⟶ S := x.1
  let A : Over S := Over.mk φ
  let t : F.obj (op A) := totalSection x rfl
  have hmap {B : Over S} (k : B ⟶ A) :
      (totalPresheaf F).map k.left.op x =
        (⟨B.hom, F.map k.op t⟩ : (totalPresheaf F).obj (op B.left)) := by
    rw [← totalMkSection (A := A) x rfl]
    exact totalMapMk k t
  refine
    { homEquiv := fun {B} =>
        Equiv.ofBijective (fun k : B ⟶ A => F.map k.op t) ⟨fun k₁ k₂ h ↦ ?_, fun y ↦ ?_⟩
      homEquiv_comp := ?_ }
  · apply Over.OverMorphism.ext
    apply R.homEquiv.injective
    have htotal : (totalPresheaf F).map k₁.left.op x =
        (totalPresheaf F).map k₂.left.op x := by
      calc
        _ = ⟨B.hom, F.map k₁.op t⟩ := hmap k₁
        _ = ⟨B.hom, F.map k₂.op t⟩ :=
          congrArg (fun z : F.obj (op B) =>
            (⟨B.hom, z⟩ : (totalPresheaf F).obj (op B.left))) h
        _ = _ := (hmap k₂).symm
    calc
      R.homEquiv k₁.left = (totalPresheaf F).map k₁.left.op x := R.homEquiv_eq _
      _ = (totalPresheaf F).map k₂.left.op x := htotal
      _ = R.homEquiv k₂.left := (R.homEquiv_eq _).symm
  · let p : (totalPresheaf F).obj (op B.left) := ⟨B.hom, y⟩
    let k₀ : B.left ⟶ W := R.homEquiv.symm p
    have hk : (totalPresheaf F).map k₀.op x = p := by
      simpa [k₀, x] using (R.homEquiv_eq k₀).symm.trans (R.homEquiv.apply_symm_apply p)
    exact ⟨Over.homMk k₀ (congrArg Sigma.fst hk), totalSigmaSndInj ((hmap _).symm.trans hk)⟩
  · intro B C b k
    change F.map (b ≫ k).op t = F.map b.op (F.map k.op t)
    rw [op_comp, Functor.map_comp]
    rfl

/-- **Representability of the total presheaf implies representability on the slice.**  This is
`Stacks.Morphisms.representableByOfTotalRepresentable` with the representing object forgotten. -/
private lemma representable_of_totalRepresentable {S : Scheme.{u}}
    {F : (Over S)ᵒᵖ ⥤ Type u} {W : Scheme.{u}}
    (R : (totalPresheaf F).RepresentableBy W) : F.IsRepresentable :=
  (representableByOfTotalRepresentable R).isRepresentable

/-- **Representability on the slice implies representability of the total presheaf.** The
representing scheme is the underlying scheme of the representing object of the slice. -/
private def totalRepresentableBy {S : Scheme.{u}} {F : (Over S)ᵒᵖ ⥤ Type u}
    {W : Over S} (R : F.RepresentableBy W) :
    (totalPresheaf F).RepresentableBy W.left := by
  let x : (totalPresheaf F).obj (op W.left) := ⟨W.hom, R.homEquiv (𝟙 W)⟩
  have hmap {A : Over S} (k : A ⟶ W) :
      (totalPresheaf F).map k.left.op x = ⟨A.hom, R.homEquiv k⟩ :=
    (totalMapMk k (R.homEquiv (𝟙 W))).trans
      (congrArg (fun z ↦ (⟨A.hom, z⟩ : (totalPresheaf F).obj (op A.left)))
        (R.homEquiv_eq k).symm)
  refine
    { homEquiv := fun {T} ↦ Equiv.ofBijective (fun k ↦ (totalPresheaf F).map k.op x) ?_
      homEquiv_comp := ?_ }
  · constructor
    · intro k l hkl
      have he : k ≫ W.hom = l ≫ W.hom := congrArg Sigma.fst hkl
      let A : Over S := Over.mk (k ≫ W.hom)
      let k' : A ⟶ W := Over.homMk k rfl
      let l' : A ⟶ W := Over.homMk l he.symm
      have hh := (hmap k').symm.trans (hkl.trans (hmap l'))
      exact congrArg Over.Hom.left (R.homEquiv.injective (totalSigmaSndInj hh))
    · rintro ⟨a, m⟩
      exact ⟨(R.homEquiv.symm m).left,
        (hmap (R.homEquiv.symm m)).trans
          (congrArg (fun z ↦ (⟨a, z⟩ : (totalPresheaf F).obj (op T)))
            (R.homEquiv.apply_symm_apply m))⟩
  · intro T T' a b
    exact (totalPresheaf F).map_comp_apply b.op a.op x

/-- **The chart morphism.** A commuting square identifying `U` above `V` with `X` above `S`
induces a morphism from the relative morphism functor of the chart to the restriction along
`CategoryTheory.Over.map i` of the relative morphism functor of `X` over `S`. -/
private def chartHom {S Z X V U : Scheme.{u}} (f : Z ⟶ S) (g : X ⟶ S)
    (i : V ⟶ S) (j : U ⟶ X) (gV : U ⟶ V) (h : gV ≫ i = j ≫ g) :
    pullbackHom (pullback.fst i f) gV ⟶ (Over.map i).op ⋙ pullbackHom f g where
  app T := ↾ fun m ↦ Over.homMk
    ((pullbackRightPullbackFstIso i f T.unop.hom).inv ≫ m.left ≫ j) (by
      change ((pullbackRightPullbackFstIso i f T.unop.hom).inv ≫ m.left ≫ j) ≫ g =
        pullback.snd (T.unop.hom ≫ i) f ≫ f
      calc
        _ = (pullbackRightPullbackFstIso i f T.unop.hom).inv ≫
            (m.left ≫ gV) ≫ i := by simp only [Category.assoc, h]
        _ = (pullbackRightPullbackFstIso i f T.unop.hom).inv ≫
            pullback.snd T.unop.hom (pullback.fst i f) ≫ pullback.fst i f ≫ i := by
          rw [show m.left ≫ gV = _ from Over.w m]; rfl
        _ = pullback.fst (T.unop.hom ≫ i) f ≫ T.unop.hom ≫ i := by simp
        _ = _ := pullback.condition)
  naturality {A B} k := by
    apply ConcreteCategory.hom_ext
    intro m
    apply Over.OverMorphism.ext
    symm
    change (pullback.lift _ _ _ ≫ (pullbackRightPullbackFstIso i f A.unop.hom).inv) ≫
      m.left ≫ j = (pullbackRightPullbackFstIso i f B.unop.hom).inv ≫
        (pullback.lift _ _ _ ≫ m.left) ≫ j
    have he : pullback.lift
        (pullback.fst (B.unop.hom ≫ i) f ≫ k.unop.left)
        (pullback.snd (B.unop.hom ≫ i) f) (by simp [Category.assoc,
          pullback.condition]) ≫ (pullbackRightPullbackFstIso i f A.unop.hom).inv =
      (pullbackRightPullbackFstIso i f B.unop.hom).inv ≫
        pullback.lift (pullback.fst B.unop.hom (pullback.fst i f) ≫ k.unop.left)
          (pullback.snd B.unop.hom (pullback.fst i f)) (by simp [Over.w k.unop,
            pullback.condition]) := by
      apply pullback.hom_ext
      · simp only [Category.assoc, pullback.lift_fst, pullbackRightPullbackFstIso_inv_fst,
          pullbackRightPullbackFstIso_inv_fst_assoc]
      · apply pullback.hom_ext
        · simp only [Category.assoc, pullback.lift_snd_assoc, pullback.lift_fst_assoc,
            pullbackRightPullbackFstIso_inv_snd_fst, Over.w k.unop]
        · simp only [Category.assoc, pullback.lift_snd, pullbackRightPullbackFstIso_inv_snd_snd]
    simpa [Category.assoc, Over.map_map_left, Functor.op] using congrArg (fun e ↦ e ≫ m.left ≫ j) he

/-- The chart morphism of total presheaves is injective at every test scheme, both components
of the chart being monomorphisms. -/
private lemma totalChart_injective {S Z X V U : Scheme.{u}} (f : Z ⟶ S) (g : X ⟶ S)
    (i : V ⟶ S) (j : U ⟶ X) (gV : U ⟶ V) (h : gV ≫ i = j ≫ g)
    [Mono i] [Mono j] (T : Scheme.{u}ᵒᵖ) :
    Function.Injective ((totalMap i (chartHom f g i j gV h)).app T) := by
  rintro ⟨a, m⟩ ⟨a', m'⟩ he
  obtain rfl : a = a' := (cancel_mono i).1 (congrArg Sigma.fst he)
  have hm := congrArg Over.Hom.left (totalSigmaSndInj (F := pullbackHom f g) (φ := a ≫ i) he)
  change (pullbackRightPullbackFstIso i f a).inv ≫ m.left ≫ j =
    (pullbackRightPullbackFstIso i f a).inv ≫ m'.left ≫ j at hm
  have hm' := (cancel_mono j).1 ((cancel_epi (pullbackRightPullbackFstIso i f a).inv).1 hm)
  exact congrArg (fun n ↦ (⟨a, n⟩ : (totalPresheaf (pullbackHom (pullback.fst i f) gV)).obj T))
    (Over.OverMorphism.ext hm')

/-- A morphism into `X` whose image lies in an open `U` factors through `U`. -/
private lemma exists_comp_ι_eq {Y X : Scheme.{u}} (U : X.Opens) (e : Y ⟶ X) (h : ∀ y, e y ∈ U) :
    ∃ l : Y ⟶ U.toScheme, l ≫ U.ι = e :=
  ⟨IsOpenImmersion.lift U.ι e (by
    rintro _ ⟨y, rfl⟩
    exact ⟨⟨e y, h y⟩, rfl⟩), IsOpenImmersion.lift_fac _ _ _⟩

/-- **The image of a chart, described pointwise.** An `S`-morphism out of `T ⨯ₛ Z` comes from the
chart exactly when `T` lands in `V` and the morphism lands in `U`. -/
private lemma totalChart_range {S Z X : Scheme.{u}} (f : Z ⟶ S) (g : X ⟶ S)
    (V : S.Opens) (U : X.Opens) (gV : U.toScheme ⟶ V.toScheme)
    (h : gV ≫ V.ι = U.ι ≫ g) {T : Scheme.{u}}
    (x : (totalPresheaf (pullbackHom f g)).obj (op T)) :
    x ∈ Set.range ((totalMap V.ι (chartHom f g V.ι U.ι gV h)).app (op T)) ↔
      (∀ t : T, x.1 t ∈ V) ∧ (∀ z, x.2.left z ∈ U) := by
  constructor
  · rintro ⟨⟨a, m⟩, rfl⟩
    exact ⟨fun t ↦ (a t).property,
      fun z ↦ (m.left ((pullbackRightPullbackFstIso V.ι f a).inv z)).property⟩
  · rintro ⟨ha, hb⟩
    obtain ⟨a, he⟩ := exists_comp_ι_eq V x.1 ha
    let A : Over S := Over.mk (a ≫ V.ι)
    let b : (pullbackHom f g).obj (op A) := totalSection x he.symm
    have hx : (⟨a ≫ V.ι, b⟩ : (totalPresheaf (pullbackHom f g)).obj (op T)) = x :=
      totalMkSection (A := A) x he.symm
    have hb' : ∀ z, b.left z ∈ U := fun z ↦ hb (((Over.pullback f).map
      (Over.homMk (𝟙 T) (by change 𝟙 T ≫ x.1 = a ≫ V.ι; simpa using he.symm) :
        A ⟶ Over.mk x.1)).left z)
    let e := pullbackRightPullbackFstIso V.ι f a
    obtain ⟨n, hn⟩ := exists_comp_ι_eq U (e.hom ≫ b.left) fun z ↦ hb' (e.hom z)
    have hnV : n ≫ gV = pullback.snd a (pullback.fst V.ι f) ≫ pullback.fst V.ι f := by
      apply (cancel_mono V.ι).1
      rw [Category.assoc, h, ← Category.assoc, hn]
      simp only [Category.assoc]
      rw [show b.left ≫ g = pullback.snd (a ≫ V.ι) f ≫ f from Over.w b]
      simp only [e, pullbackRightPullbackFstIso_hom_snd_assoc]
      rw [pullback.condition]
    refine ⟨⟨a, Over.homMk n hnV⟩, ?_⟩
    apply Eq.trans _ hx
    apply congrArg (fun b ↦ (⟨a ≫ V.ι, b⟩ :
      (totalPresheaf (pullbackHom f g)).obj (op T)))
    apply Over.OverMorphism.ext
    show e.inv ≫ n ≫ U.ι = b.left
    rw [hn, Iso.inv_hom_id_assoc]

/-- **The image of a chart, as an open condition on the test scheme.** A restriction of an
element of the total presheaf along `e : T' ⟶ T` comes from the chart exactly when `e` lands in
`Stacks.Morphisms.goodOpen`. -/
private lemma totalChart_range_map {S Z X T T' : Scheme.{u}}
    (f : Z ⟶ S) (g : X ⟶ S) [IsFiniteLocallyFree f]
    (V : S.Opens) (U : X.Opens) (gV : U.toScheme ⟶ V.toScheme)
    (h : gV ≫ V.ι = U.ι ≫ g)
    (x : (totalPresheaf (pullbackHom f g)).obj (op T))
    (e : T' ⟶ T) :
    letI : UniversallyClosed (pullback.fst x.1 f) := universallyClosed_pullback f x.1
    (totalPresheaf (pullbackHom f g)).map e.op x ∈
      Set.range ((totalMap V.ι (chartHom f g V.ι U.ι gV h)).app (op T')) ↔
      ∀ t : T', e t ∈ goodOpen x.1 (pullback.fst x.1 f) x.2.left V U := by
  let : UniversallyClosed (pullback.fst x.1 f) := universallyClosed_pullback f x.1
  rw [totalChart_range]
  let k : Over.mk (e ≫ x.1) ⟶ Over.mk x.1 := Over.homMk e rfl
  let p : pullback (e ≫ x.1) f ⟶ pullback x.1 f :=
    ((Over.pullback f).map k).left
  show (∀ t, x.1 (e t) ∈ V) ∧ (∀ z, x.2.left (p z) ∈ U) ↔ _
  have hfst : p ≫ pullback.fst x.1 f = pullback.fst (e ≫ x.1) f ≫ e := by
    simp only [p, k, Over.pullback_map_left]
    exact pullback.lift_fst _ _ _
  have hp : IsPullback (pullback.fst (e ≫ x.1) f) p e (pullback.fst x.1 f) := by
    convert (IsPullback.of_hasPullback x.1 f).paste_vert_iff
      (show pullback.fst (e ≫ x.1) f ≫ e = p ≫ pullback.fst x.1 f from hfst.symm)
        |>.1 ?_ using 1
    simpa [p, k, Over.pullback_map_left, pullback.lift_snd] using
      IsPullback.of_hasPullback (e ≫ x.1) f
  constructor
  · rintro ⟨ha, hb⟩ t
    apply (mem_goodOpen _ _ _ _ _ _).2
    refine ⟨ha t, fun y hy ↦ ?_⟩
    obtain ⟨z, hz, hzy⟩ := Scheme.exists_preimage_of_isPullback hp t y hy.symm
    exact hzy ▸ hb z
  · exact fun hh ↦ ⟨fun t ↦ ((mem_goodOpen _ _ _ _ _ _).1 (hh t)).1, fun z ↦
      ((mem_goodOpen _ _ _ _ _ _).1 (hh (pullback.fst (e ≫ x.1) f z))).2 (p z)
        (congrArg (fun q : pullback (e ≫ x.1) f ⟶ T ↦ q z) hfst)⟩

/-- **A criterion for a morphism from a representable presheaf to be an open immersion of
presheaves**: it is injective at every test scheme, and its image over a test scheme is cut out by
an open subscheme of it. -/
private lemma openImmersion_presheaf_of_range {F : Scheme.{u}ᵒᵖ ⥤ Type u}
    {W : Scheme.{u}} (η : yoneda.obj W ⟶ F)
    (hinj : ∀ T, Function.Injective (η.app T))
    (hopen : ∀ (T : Scheme.{u}) (x : F.obj (op T)),
      ∃ O : T.Opens, ∀ (T' : Scheme.{u}) (e : T' ⟶ T),
        (∃ k : T' ⟶ W, η.app _ k = F.map e.op x) ↔ ∀ t, e t ∈ O) :
    IsOpenImmersion.presheaf η := by
  apply MorphismProperty.relative.of_exists
  intro T ζ
  obtain ⟨O, hO⟩ := hopen T (yonedaEquiv ζ)
  obtain ⟨k, hk⟩ := (hO O.toScheme O.ι).2 (fun t ↦ t.property)
  have comm : yoneda.map k ≫ η = yoneda.map O.ι ≫ ζ := by
    apply yonedaEquiv.injective
    simpa only [yonedaEquiv_comp, yonedaEquiv_yoneda_map] using hk.trans (map_yonedaEquiv _ _)
  refine ⟨O.toScheme, yoneda.map k, O.ι, ?_, inferInstance⟩
  apply IsPullback.iff_app.mpr
  intro T'
  apply (Types.isPullback_iff _ _ _ _).2
  refine ⟨congrArg (fun n ↦ n.app T') comm, ?_, ?_⟩
  · exact fun a b hab ↦ (cancel_mono O.ι).1 hab.2
  · intro a e he
    change T'.unop ⟶ W at a
    change T'.unop ⟶ T at e
    have heO : ∀ t, e t ∈ O := (hO T'.unop e).1
      ⟨a, he.trans (map_yonedaEquiv _ _).symm⟩
    obtain ⟨l, hl⟩ := exists_comp_ι_eq O e heO
    refine ⟨l, ?_, hl⟩
    apply hinj T'
    have hc := congrArg (fun n : yoneda.obj O.toScheme ⟶ F ↦ n.app T' l) comm
    change η.app T' (l ≫ k) = ζ.app T' (l ≫ O.ι) at hc
    exact hc.trans ((congrArg (ζ.app T') hl).trans he.symm)

/-- **A finite set inside an affine open and inside another open lies in an affine open contained
in the latter.** The elements of `Γ(X, U)` whose basic open lies in `V` form an ideal not covered
by the finitely many primes of the points of `E`, by prime avoidance, so one of them cuts out a
basic open of `U` containing `E` and contained in `V`. -/
private lemma exists_affineOpen_between {X : Scheme.{u}} {U V : X.Opens}
    (hU : IsAffineOpen U) {E : Set X} (hE : E.Finite) (hEU : E ⊆ U) (hEV : E ⊆ V) :
    ∃ W : X.Opens, IsAffineOpen W ∧ E ⊆ W ∧ W ≤ V := by
  classical
  by_cases hne : E.Nonempty
  · let I : Ideal Γ(X, U) :=
      { carrier := {r | X.basicOpen r ≤ V}
        zero_mem' := by simp
        add_mem' := fun hr hs ↦ (X.basicOpen_add_le _ _).trans (sup_le hr hs)
        smul_mem' := fun r s hs ↦ by
          show X.basicOpen (r * s) ≤ V
          rw [Scheme.basicOpen_mul]
          exact inf_le_of_right_le hs }
    let p : E → PrimeSpectrum Γ(X, U) := fun x ↦ hU.primeIdealOf ⟨x.1, hEU x.2⟩
    have hp (x : E) (r : Γ(X, U)) : r ∉ (p x).asIdeal ↔ x.1 ∈ X.basicOpen r := by
      show p x ∈ PrimeSpectrum.basicOpen r ↔ _
      rw [← hU.fromSpec_preimage_basicOpen]
      show hU.fromSpec (p x) ∈ X.basicOpen r ↔ _
      rw [IsAffineOpen.fromSpec_primeIdealOf]
    let x₀ : E := ⟨hne.choose, hne.choose_spec⟩
    have hn : ¬ (I : Set Γ(X, U)) ⊆ ⋃ x ∈ (Set.univ : Set E), ((p x).asIdeal : Set Γ(X, U)) := by
      let := hE.fintype
      rw [Ideal.subset_union_prime_finite (Set.toFinite (Set.univ : Set E)) x₀ x₀
        (fun x _ _ _ ↦ (p x).isPrime)]
      rintro ⟨x, _, hx⟩
      obtain ⟨r, hr, hxr⟩ := hU.exists_basicOpen_le ⟨x.1, hEV x.2⟩ (hEU x.2)
      exact (hp x r).2 hxr (hx hr)
    obtain ⟨r, hr, havoid⟩ := Set.not_subset.mp hn
    refine ⟨X.basicOpen r, hU.basicOpen r, ?_, hr⟩
    intro x hx
    apply (hp ⟨x, hx⟩ r).1
    intro hrp
    exact havoid (Set.mem_iUnion.2 ⟨⟨x, hx⟩, Set.mem_iUnion.2 ⟨Set.mem_univ _, hrp⟩⟩)
  · refine ⟨⊥, ?_, ?_, bot_le⟩
    · simpa using hU.basicOpen (0 : Γ(X, U))
    · exact fun z hz ↦ (hne ⟨z, hz⟩).elim

/-! ### The affine charts -/

/-- **The index of an affine chart.** An affine open `V` of the base over which the base change
of `f` has finite free global sections, together with an affine open `U` of `X` lying above `V`.

The two module-theoretic fields are the hypotheses of Stacks Tag 05Y6, and they are what
restricts `V`: finite local freeness of `f` only makes `f_* 𝒪_Z` free locally on the base. They
are available at every point of the base by
`Stacks.Morphisms.exists_isAffineOpen_module_finite_and_free`. -/
private structure AffineChartIndex {S Z X : Scheme.{u}} (f : Z ⟶ S) (g : X ⟶ S) where
  /-- The affine open of the base. -/
  V : S.Opens
  /-- Affineness of `V`. -/
  hV : IsAffineOpen V
  /-- The affine open of `X`. -/
  U : X.Opens
  /-- Affineness of `U`. -/
  hU : IsAffineOpen U
  /-- `U` lies above `V`. -/
  hfactor : U ≤ g ⁻¹ᵁ V
  /-- The global sections of the base change of `f` to `V` form a finite module. -/
  hfinite : letI := (pullback.fst V.ι f).appTop.hom.toAlgebra
    Module.Finite Γ(V.toScheme, ⊤) Γ(pullback V.ι f, ⊤)
  /-- The global sections of the base change of `f` to `V` form a free module. -/
  hfree : letI := (pullback.fst V.ι f).appTop.hom.toAlgebra
    Module.Free Γ(V.toScheme, ⊤) Γ(pullback V.ι f, ⊤)

/-- The morphism `U ⟶ V` through which `U ⟶ X ⟶ S` factors, the factorisation being the
defining property of the chart index. -/
private def affineChartMapToBase {S Z X : Scheme.{u}} {f : Z ⟶ S} {g : X ⟶ S}
    (i : AffineChartIndex f g) : i.U.toScheme ⟶ i.V.toScheme :=
  (exists_comp_ι_eq i.V (i.U.ι ≫ g) fun y ↦ i.hfactor y.2).choose

/-- The defining factorisation of `Stacks.Morphisms.affineChartMapToBase`. -/
private lemma affineChartMapToBase_fac {S Z X : Scheme.{u}} {f : Z ⟶ S} {g : X ⟶ S}
    (i : AffineChartIndex f g) : affineChartMapToBase i ≫ i.V.ι = i.U.ι ≫ g :=
  (exists_comp_ι_eq i.V (i.U.ι ≫ g) fun y ↦ i.hfactor y.2).choose_spec

/-- **Over an affine chart the relative morphism functor is represented by the spectrum of a
ring of bounded cardinality.** This is Stacks Tag 05Y6 in the form
`AlgebraicGeometry.relativeHom_representableBy_affine_mk_le`: the base `V` and the target `U` are
affine, the base change of `Z` is affine because the base change of `f` is an affine morphism,
and its global sections are finite free by the corresponding fields of the chart index. -/
private lemma exists_affineChartData {S Z X : Scheme.{u}}
    (f : Z ⟶ S) (g : X ⟶ S) [IsFiniteLocallyFree f] (i : AffineChartIndex f g) :
    ∃ (W : Scheme.{u}) (Q : Type u) (_ : CommRing Q),
      #Q ≤ #Γ(i.U.toScheme, ⊤) ⊔ #Γ(i.V.toScheme, ⊤) ⊔ ℵ₀ ∧
      Nonempty (W ≅ Spec (CommRingCat.of Q)) ∧
      Nonempty ((totalPresheaf (pullbackHom (pullback.fst i.V.ι f)
        (affineChartMapToBase i))).RepresentableBy W) := by
  let : IsFiniteLocallyFree (pullback.fst i.V.ι f) := isFiniteLocallyFree_pullback_fst f i.V.ι
  let : IsAffine i.V.toScheme := i.hV
  let : IsAffine i.U.toScheme := i.hU
  let : IsAffine (pullback i.V.ι f) := isAffine_of_isAffineHom (pullback.fst i.V.ι f)
  obtain ⟨W, Q, _, -, hQ, ⟨eQ⟩, ⟨r⟩⟩ :=
    AlgebraicGeometry.relativeHom_representableBy_affine_mk_le i.V.toScheme
      (pullback i.V.ι f) i.U.toScheme (pullback.fst i.V.ι f) (affineChartMapToBase i)
      i.hfinite i.hfree
  exact ⟨W.left, Q, inferInstance, hQ, ⟨eQ⟩,
    ⟨totalRepresentableBy (r.ofIso (pullbackHomIso _ _))⟩⟩

/-- **Over an affine chart the relative morphism functor is representable.** The representing
scheme of `Stacks.Morphisms.exists_affineChartData`. -/
private def affineChartRepresentingData {S Z X : Scheme.{u}}
    (f : Z ⟶ S) (g : X ⟶ S) [IsFiniteLocallyFree f] (i : AffineChartIndex f g) :
    Σ W : Scheme.{u},
      (totalPresheaf (pullbackHom (pullback.fst i.V.ι f)
        (affineChartMapToBase i))).RepresentableBy W :=
  ⟨(exists_affineChartData f g i).choose,
    (exists_affineChartData f g i).choose_spec.choose_spec.choose_spec.2.2.some⟩

/-- **The representing scheme of a chart is the spectrum of a ring of bounded cardinality.** -/
private lemma affineChartRepresentingData_spec {S Z X : Scheme.{u}}
    (f : Z ⟶ S) (g : X ⟶ S) [IsFiniteLocallyFree f] (i : AffineChartIndex f g) :
    ∃ (Q : Type u) (_ : CommRing Q),
      #Q ≤ #Γ(i.U.toScheme, ⊤) ⊔ #Γ(i.V.toScheme, ⊤) ⊔ ℵ₀ ∧
      Nonempty ((affineChartRepresentingData f g i).1 ≅ Spec (CommRingCat.of Q)) :=
  ⟨(exists_affineChartData f g i).choose_spec.choose,
    (exists_affineChartData f g i).choose_spec.choose_spec.choose,
    (exists_affineChartData f g i).choose_spec.choose_spec.choose_spec.1,
    (exists_affineChartData f g i).choose_spec.choose_spec.choose_spec.2.1⟩

/-- **A chart index is determined by its two affine opens**, the remaining fields being
propositions. -/
private lemma affineChartIndex_injective {S Z X : Scheme.{u}} (f : Z ⟶ S) (g : X ⟶ S) :
    Function.Injective (fun i : AffineChartIndex f g =>
      ((⟨i.V, i.hV⟩ : S.affineOpens), (⟨i.U, i.hU⟩ : X.affineOpens))) := by
  rintro ⟨V, hV, U, hU, h₁, h₂, h₃⟩ ⟨V', hV', U', hU', h₁', h₂', h₃'⟩ h
  obtain ⟨hVV, hUU⟩ := Prod.mk.injEq .. ▸ h
  obtain rfl : V = V' := congrArg Subtype.val hVV
  obtain rfl : U = U' := congrArg Subtype.val hUU
  rfl

/-- The chart, as a morphism from a representable presheaf into the total presheaf. -/
private def affineChartToTotal {S Z X : Scheme.{u}} (f : Z ⟶ S) (g : X ⟶ S)
    [IsFiniteLocallyFree f] (i : AffineChartIndex f g) :
    yoneda.obj (affineChartRepresentingData f g i).1 ⟶ totalPresheaf (pullbackHom f g) :=
  (affineChartRepresentingData f g i).2.toIso.hom ≫
    totalMap i.V.ι (chartHom f g i.V.ι i.U.ι (affineChartMapToBase i)
      (affineChartMapToBase_fac i))

/-- The image of a chart is the image of the chart morphism of total presheaves, the
representability isomorphism being bijective. -/
private lemma affineChartToTotal_range {S Z X : Scheme.{u}} (f : Z ⟶ S) (g : X ⟶ S)
    [IsFiniteLocallyFree f] (i : AffineChartIndex f g) (T : Scheme.{u}ᵒᵖ)
    (x : (totalPresheaf (pullbackHom f g)).obj T) :
    x ∈ Set.range ((affineChartToTotal f g i).app T) ↔
      x ∈ Set.range ((totalMap i.V.ι (chartHom f g i.V.ι i.U.ι
        (affineChartMapToBase i) (affineChartMapToBase_fac i))).app T) := by
  let R := (affineChartRepresentingData f g i).2
  constructor
  · exact fun ⟨k, hk⟩ ↦ ⟨R.homEquiv k, hk⟩
  · rintro ⟨m, hm⟩
    refine ⟨R.homEquiv.symm m, ?_⟩
    show (totalMap i.V.ι (chartHom f g i.V.ι i.U.ι
      (affineChartMapToBase i) (affineChartMapToBase_fac i))).app T
        (R.homEquiv (R.homEquiv.symm m)) = x
    rwa [Equiv.apply_symm_apply]

/-- **Each chart is an open immersion of presheaves.** Injectivity is
`Stacks.Morphisms.totalChart_injective`, and the image is cut out by
`Stacks.Morphisms.goodOpen` by `Stacks.Morphisms.totalChart_range_map`. -/
private lemma affineChartToTotal_open {S Z X : Scheme.{u}} (f : Z ⟶ S) (g : X ⟶ S)
    [IsFiniteLocallyFree f] (i : AffineChartIndex f g) :
    IsOpenImmersion.presheaf (affineChartToTotal f g i) := by
  apply openImmersion_presheaf_of_range
  · intro T
    exact (totalChart_injective f g i.V.ι i.U.ι (affineChartMapToBase i)
      (affineChartMapToBase_fac i) T).comp
      (affineChartRepresentingData f g i).2.homEquiv.injective
  · intro T x
    let : UniversallyClosed (pullback.fst x.1 f) := universallyClosed_pullback f x.1
    refine ⟨goodOpen x.1 (pullback.fst x.1 f) x.2.left i.V i.U, fun T' e ↦ ?_⟩
    exact (affineChartToTotal_range f g i _ _).trans
      (totalChart_range_map f g i.V i.U (affineChartMapToBase i)
        (affineChartMapToBase_fac i) x e)

/-- **The charts cover.** The image under `b` of the fibre of `T ⨯ₛ Z` over a point `t` of `T` is
a finite subset of one fibre of `g`, so the hypothesis of Stacks Tag 0BL4 puts it inside an affine
open of `X`; shrinking that open into the preimage of an affine open `V` over which the base
change of `f` is finite free produces a chart whose open locus contains `t`. -/
private lemma affineChart_cover {S Z X : Scheme.{u}} (f : Z ⟶ S) (g : X ⟶ S)
    [IsFiniteLocallyFree f]
    (hX : ∀ (s : S) (t : Set X), t.Finite → (∀ x ∈ t, g.base x = s) →
      ∃ U : X.Opens, IsAffineOpen U ∧ t ⊆ U)
    {T : Scheme.{u}} (x : (totalPresheaf (pullbackHom f g)).obj (op T)) (t : T) :
    letI : UniversallyClosed (pullback.fst x.1 f) := universallyClosed_pullback f x.1
    ∃ i : AffineChartIndex f g, t ∈ goodOpen x.1 (pullback.fst x.1 f) x.2.left i.V i.U := by
  let : UniversallyClosed (pullback.fst x.1 f) := universallyClosed_pullback f x.1
  let E : Set X := x.2.left '' ((pullback.fst x.1 f) ⁻¹' {t})
  have hE : E.Finite := (finite_fiber_pullback f x.1 t).image x.2.left
  have hbase : ∀ z ∈ E, g z = x.1 t := by
    rintro z ⟨y, hy, rfl⟩
    have hc : x.2.left ≫ g = pullback.fst x.1 f ≫ x.1 :=
      (Over.w x.2).trans pullback.condition.symm
    show g (x.2.left y) = x.1 t
    exact (congrArg (fun k : pullback x.1 f ⟶ S ↦ k y) hc).trans
        (congrArg (fun z ↦ x.1 z) hy)
  obtain ⟨V, hV, htV, hVfinite, hVfree⟩ :=
    exists_isAffineOpen_module_finite_and_free f (x.1 t)
  obtain ⟨U₀, hU₀, hEU₀⟩ := hX (x.1 t) E hE hbase
  have hEV : E ⊆ g ⁻¹ᵁ V := by
    intro z hz
    show g z ∈ V
    rwa [hbase z hz]
  obtain ⟨U, hU, hEU, hUV⟩ := exists_affineOpen_between hU₀ hE hEU₀ hEV
  exact ⟨⟨V, hV, U, hU, hUV, hVfinite, hVfree⟩,
    (mem_goodOpen _ _ _ _ _ _).2 ⟨htV, fun y hy ↦ hEU ⟨y, hy, rfl⟩⟩⟩

/-- **The charts are jointly locally surjective for the Zariski topology.** The open loci of the
charts cover every test scheme by `Stacks.Morphisms.affineChart_cover`, and on each of them the
restriction of the given element comes from the chart. -/
private lemma affineCharts_locallySurjective {S Z X : Scheme.{u}} (f : Z ⟶ S) (g : X ⟶ S)
    [IsFiniteLocallyFree f]
    (hX : ∀ (s : S) (t : Set X), t.Finite → (∀ x ∈ t, g.base x = s) →
      ∃ U : X.Opens, IsAffineOpen U ∧ t ⊆ U) :
    Presheaf.IsLocallySurjective Scheme.zariskiTopology
      (Sigma.desc (affineChartToTotal f g)) := by
  constructor
  intro T x
  let : UniversallyClosed (pullback.fst x.1 f) := universallyClosed_pullback f x.1
  let O (i : AffineChartIndex f g) : T.Opens :=
    goodOpen x.1 (pullback.fst x.1 f) x.2.left i.V i.U
  let 𝒰 : T.OpenCover := Scheme.Cover.mkOfCovers (AffineChartIndex f g)
    (fun i ↦ (O i).toScheme) (fun i ↦ (O i).ι) (by
      intro t
      obtain ⟨i, hi⟩ := affineChart_cover f g hX x t
      exact ⟨i, ⟨t, hi⟩, rfl⟩)
  apply Scheme.zariskiTopology.superset_covering ?_ 𝒰.mem_grothendieckTopology
  rw [Sieve.ofArrows, Sieve.generate_le_iff]
  rintro _ _ ⟨i⟩
  obtain ⟨k, hk⟩ : (totalPresheaf (pullbackHom f g)).map (O i).ι.op x ∈
      Set.range ((affineChartToTotal f g i).app (op (O i).toScheme)) :=
    (affineChartToTotal_range f g i _ _).mpr
      ((totalChart_range_map f g i.V i.U (affineChartMapToBase i)
        (affineChartMapToBase_fac i) x (O i).ι).mpr (fun t ↦ t.property))
  exact ⟨(Sigma.ι (fun i ↦ yoneda.obj (affineChartRepresentingData f g i).1) i).app _ k,
    (congrArg (fun n : yoneda.obj (affineChartRepresentingData f g i).1 ⟶
      totalPresheaf (pullbackHom f g) ↦ n.app (op (O i).toScheme) k)
      (Sigma.ι_desc (affineChartToTotal f g) i)).trans hk⟩

/-- **Stacks Project, Tag 0BL4, with the representing object and the affine charts it is glued
from.** If `Z` is finite locally free over `S` and every finite set of points in a fibre of `X`
lies in an affine open of `X`, then the functor of `S`-morphisms from `Z` to `X` is represented
by an object `W` of the category of schemes over `S`, and the scheme underlying `W` carries an
open covering by the affine charts of Stacks Tag 05Y6 — one for each pair of an affine open of
`S` over which the base change of `f` is finite free and an affine open of `X` above it.

Each chart is the spectrum of a ring of cardinality at most that of the global sections of the
two affine opens it is indexed by, and the index type injects into the pairs of affine opens. So
this says, beyond representability, that the representing object is built from pieces no larger
than `S` and `X`, which is what bounds its size.

`Stacks.Morphisms.homFromFiniteLocallyFree_isRepresentable` is the plain representability
statement, which is the source's assertion. -/
@[sga "3 XI 3.13" "partial"]
theorem homFromFiniteLocallyFree_representableBy
    {S Z X : Scheme.{u}} (f : Z ⟶ S) (g : X ⟶ S)
    [IsFiniteLocallyFree f]
    (hX : ∀ (s : S) (t : Set X), t.Finite →
      (∀ x ∈ t, g.base x = s) →
      ∃ U : X.Opens, IsAffineOpen U ∧ t ⊆ U) :
    ∃ (W : Over S) (ι : Type u) (Y : ι → Scheme.{u}) (a : ∀ i, Y i ⟶ W.left),
      #ι ≤ #S.affineOpens ⊔ #X.affineOpens ⊔ ℵ₀ ∧
      (∀ i, ∃ (Q : Type u) (_ : CommRing Q) (V : S.affineOpens) (U : X.affineOpens),
        #Q ≤ #Γ(U.1.toScheme, ⊤) ⊔ #Γ(V.1.toScheme, ⊤) ⊔ ℵ₀ ∧
          Nonempty (Y i ≅ Spec (CommRingCat.of Q))) ∧
      (∀ i, IsOpenImmersion (a i)) ∧
      (∀ y : W.left, ∃ i, y ∈ Set.range (a i).base) ∧
      Nonempty (((prod.functor.obj (Over.mk f)).op ⋙
        yoneda.obj (Over.mk g)).RepresentableBy W) := by
  let H := totalPresheaf (pullbackHom f g)
  let F : Sheaf Scheme.zariskiTopology (Type u) :=
    ⟨H, (isSheaf_iff_isSheaf_of_type _ _).2 (totalPullbackHom_isSheaf f g)⟩
  let := affineCharts_locallySurjective f g hX
  let hfo : ∀ i, IsOpenImmersion.presheaf (affineChartToTotal f g i) :=
    affineChartToTotal_open f g
  let RB : H.RepresentableBy
      (Scheme.LocalRepresentability.glueData (F := F) hfo).glued :=
    Scheme.LocalRepresentability.representableBy (F := F) hfo
  refine ⟨Over.mk (RB.homEquiv (𝟙 _)).1, AffineChartIndex f g,
    fun i => (affineChartRepresentingData f g i).1,
    fun i => Scheme.LocalRepresentability.toGlued (F := F) hfo i, ?_, ?_,
    fun i => inferInstance, ?_,
    ⟨(representableByOfTotalRepresentable RB).ofIso (pullbackHomIso f g).symm⟩⟩
  · exact (mk_le_of_injective (affineChartIndex_injective f g)).trans
      (((mk_prod _ _).trans_le (by
          simpa only [lift_id] using mul_le_max #S.affineOpens #X.affineOpens)).trans
        (sup_le (sup_le (le_sup_of_le_left le_sup_left) (le_sup_of_le_left le_sup_right))
          le_sup_right))
  · intro i
    obtain ⟨Q, _, hQ, e⟩ := affineChartRepresentingData_spec f g i
    exact ⟨Q, inferInstance, ⟨i.V, i.hV⟩, ⟨i.U, i.hU⟩, hQ, e⟩
  · intro y
    obtain ⟨p, hp⟩ :=
      (Scheme.LocalRepresentability.glueData (F := F) hfo).openCover.covers y
    exact ⟨(Scheme.LocalRepresentability.glueData (F := F) hfo).openCover.idx y, p, hp⟩

/-- **Stacks Project, Tag 0BL4.** If `Z` is finite locally free over `S` and every finite set of
points in a fibre of `X` lies in an affine open of `X`, then the functor of `S`-morphisms from
`Z` to `X` is representable. -/
@[stacks 0BL4]
theorem homFromFiniteLocallyFree_isRepresentable
    {S Z X : Scheme.{u}} (f : Z ⟶ S) (g : X ⟶ S)
    [IsFiniteLocallyFree f]
    (hX : ∀ (s : S) (t : Set X), t.Finite →
      (∀ x ∈ t, g.base x = s) →
      ∃ U : X.Opens, IsAffineOpen U ∧ t ⊆ U) :
    ((prod.functor.obj (Over.mk f)).op ⋙ yoneda.obj (Over.mk g)).IsRepresentable := by
  obtain ⟨W, -, -, -, -, -, -, -, ⟨r⟩⟩ := homFromFiniteLocallyFree_representableBy f g hX
  exact r.isRepresentable

/-- **Stacks Project, Tag 0BL5.** If `Z` is finite locally free over `S` and `X` is separated
and quasi-finite over `S`, then the functor of `S`-morphisms from `Z` to `X` is representable.

The hypothesis of Stacks Tag 0BL4 is supplied by Stacks Tag 07S0: a finite set of points of `X`
in one fibre over `s : S` lies above an affine open `U ∋ s`, so it is a finite set of points of
`g ⁻¹ᵁ U`, which is separated and quasi-finite over the affine scheme `U`. -/
@[stacks 0BL5]
theorem relativeHom_isRepresentable_of_locallyQuasiFinite
    {S Z X : Scheme.{u}} (f : Z ⟶ S) (g : X ⟶ S)
    [IsFiniteLocallyFree f] [IsSeparated g] [LocallyOfFiniteType g] [LocallyQuasiFinite g] :
    ((prod.functor.obj (Over.mk f)).op ⋙ yoneda.obj (Over.mk g)).IsRepresentable := by
  refine homFromFiniteLocallyFree_isRepresentable f g fun s t ht hbase ↦ ?_
  obtain ⟨-, ⟨U, hU, rfl⟩, hsU, -⟩ :=
    S.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ s) isOpen_univ
  have : IsAffine U := hU
  have ht' : Finite t := ht.to_subtype
  let q : t → (g ⁻¹ᵁ U).toScheme := fun x ↦ ⟨x.1, show g.base x.1 ∈ U from hbase x.1 x.2 ▸ hsU⟩
  obtain ⟨W, hW, hsub⟩ := exists_isAffineOpen_containing_finite_of_locallyQuasiFinite
    (g ∣_ U) (Set.finite_range q)
  exact ⟨(g ⁻¹ᵁ U).ι ''ᵁ W, hW.image_of_isOpenImmersion _,
    fun x hx ↦ ⟨q ⟨x, hx⟩, hsub ⟨⟨x, hx⟩, rfl⟩, rfl⟩⟩

end Stacks.Morphisms

end
