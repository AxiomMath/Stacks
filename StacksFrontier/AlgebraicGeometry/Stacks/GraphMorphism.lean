module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.FibreProductComparison
public import StacksFrontier.AlgebraicGeometry.Stacks.FibreProductComparisonFiniteType
public import StacksFrontier.AlgebraicGeometry.Stacks.FibreProductComparisonSeparation
public import StacksFrontier.AlgebraicGeometry.Stacks.RepresentabilityInvariance
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativePropertyInvariance
public import StacksFrontier.CategoryTheory.TwoFibreProduct.OverBase
public import StacksFrontier.CategoryTheory.TwoFibreProduct.OverTautologicalPoint
public import StacksFrontier.CategoryTheory.TwoFibreProductOverReindex

/-!
# The graph of a 1-morphism of algebraic stacks (Stacks 050I)

Let `g : 𝒳 ⟶ 𝒴` be a 1-morphism of algebraic stacks over `S`, let `p : 𝒳 ⟶ 𝒯` and `q : 𝒴 ⟶ 𝒯` be
1-morphisms to a third algebraic stack and let `η : p ≅ g ≫ q` be a 2-isomorphism exhibiting `g`
as a 1-morphism over `𝒯`. The **graph** of `g` over `𝒯` is the 1-morphism
`Γ_g : 𝒳 ⟶ 𝒳 ×_𝒯 𝒴` mediating the cone with projections `𝟙 𝒳` and `g`. The filler of that cone
names `CategoryTheory.Bicategory.leftUnitor` in full rather than using its notation, which the
repository style checker reads as a `fun` binder.

**Stacks 050I** asserts that `Γ_g` is representable by algebraic spaces and locally of finite
type, and that it inherits stronger properties from `q`. All five parts are proved here: `Γ_g` is
representable by algebraic spaces and locally of finite type, it is unramified in the relative
sense of Stacks 03YK as soon as `q` is Deligne–Mumford, and in the sense of Properties of Stacks,
Section 04XB it is locally quasi-finite as soon as `q` is quasi-DM, proper as soon as `q` is
separated, and quasi-compact and quasi-separated as soon as `q` is quasi-separated.

## Main definitions

* `AlgebraicGeometry.Stack.graphCone`: the 2-commutative square over the cospan `(p, q)` with
  apex `𝒳`, projections `𝟙 𝒳` and `g`, and filler built from `η`.
* `AlgebraicGeometry.Stack.graph`: the graph itself, the mediating 1-morphism of that cone into
  the 2-fibre product of Stacks 04T2.
* `AlgebraicGeometry.Stack.graph_fst_iso` and `AlgebraicGeometry.Stack.graph_snd_iso`: the two
  comparison 2-isomorphisms identifying the projections of the graph with `𝟙 𝒳` and with `g`.

## Main results

* `AlgebraicGeometry.Stack.isRepresentableByAlgebraicSpaces_graph` and
  `AlgebraicGeometry.Stack.isLocallyOfFiniteType_graph`: **Stacks 050I**, the two halves of
  part (1).
* `AlgebraicGeometry.Stack.relativeProperty_graph_of_comparison`: transfer of the longhand
  quantifier of Stacks 03YK from the comparison 1-morphism of Stacks 050H to the graph, with no
  hypothesis on the property, and `.hasRelativeProperty_graph_of_comparison`: the same through
  the abbreviation `AlgebraicGeometry.Stack.HasRelativeProperty`.
* `AlgebraicGeometry.Stack.isUnramified_graph`: **Stacks 050I**, part (2).
* `AlgebraicGeometry.Stack.isLocallyQuasiFinite_graph`: **Stacks 050I**, part (3).
* `AlgebraicGeometry.Stack.isProper_graph`: **Stacks 050I**, part (4).
* `AlgebraicGeometry.Stack.isQuasiCompact_graph` and
  `AlgebraicGeometry.Stack.isQuasiSeparated_graph`: **Stacks 050I**, the two halves of part (5).

## Implementation notes

The whole argument runs through the comparison 1-morphism `i : 𝒳 ×_𝒴 𝒴 ⟶ 𝒳 ×_𝒯 𝒴` of Stacks
050H: the graph is 2-isomorphic to the composite of `i` with two *equivalences*, so Stacks 0457
and Stacks 0459 carry representability and any relative property from `i` to it. The two
equivalences are

* the identification of `𝒳 ×_{g, 𝒴, 𝟙 𝒴} 𝒴` with `𝒳` — the 2-fibre product along an identity leg
  is the source, `identityGraphEquivalence` below, whose inverse is the tautological point
  `CategoryTheory.TwoFibreProductOver.pointOfFunctor` of `g` taken at the identity leg; and
* the reindexing `CategoryTheory.TwoFibreProductOver.reindexSymm` of the 2-fibre product along
  the 2-isomorphism `η`, which turns the product taken along `g ≫ q` into the one taken along
  `p`. That both reindexing functors are mutually inverse *as functors*, and hence equivalences,
  is `CategoryTheory.TwoFibreProductOver.reindexSymm_comp_reindex` and
  `.isEquivalence_reindex` in `StacksFrontier.CategoryTheory.TwoFibreProductOverReindex`, beside the
  object-level statements they strengthen.

The two `eqToHom`-component lemmas that reindexing argument needs also live there, as
`CategoryTheory.TwoFibreProductOver.Hom.a_eqToHom` and `.Hom.b_eqToHom`. They duplicate
`CategoryTheory.TwoFibreProductOver.eqToHom_a` and `.eqToHom_b` of
`StacksFrontier.CategoryTheory.TwoFibreProductOverRelocalize`, which are stated only for a base
category of the form `CategoryTheory.Over Y`; the general pair cannot be deleted in favour of that
specialisation, and generalising the specialisation in place is a change to that module.

The transfer is stated twice. `AlgebraicGeometry.Stack.relativeProperty_graph_of_comparison`
writes the quantifier of Stacks 03YK out by hand, and
`AlgebraicGeometry.Stack.hasRelativeProperty_graph_of_comparison` is the same statement through
the abbreviation `AlgebraicGeometry.Stack.HasRelativeProperty`, which carries
`[P.IsStableUnderBaseChange]` and `[P.IsLocalAtTarget …]` as instance arguments. The argument
uses neither — it is `AlgebraicGeometry.Stack.relativeProperty_of_equivalences`, which needs no
hypothesis on the property — and the four conditions of Stacks 04YW and the six properties of
Section 04XB are stated with the longhand quantifier for exactly that reason, so the longhand
form is the one a consumer can apply. This is the pattern of
`AlgebraicGeometry.Stack.relativeProperty_baseChange` and
`.hasRelativeProperty_baseChange` for Stacks 045C.

Because the transfer is used in its longhand form, part (1)'s locally-of-finite-type half and
parts (3), (4) and (5) need no instance of Stacks 03YK at all: their only inputs are the
corresponding assertions of Stacks 050H about the comparison 1-morphism, which are stated with
the same longhand quantifier. In particular the fppf `MorphismProperty.IsLocalAtTarget`
instances of Stacks 0422, Stacks 041N and Stacks 041S, and the packaged local quasi-finiteness
of Stacks 06MF, are not needed, and neither are Stacks 041L and Stacks 03HF for the
quasi-compactness half of part (5).

Part (1)'s locally-of-finite-type half uses the corresponding half of Stacks 050H, which is
`AlgebraicGeometry.Stack.isLocallyOfFiniteType_comparison` of
`StacksFrontier/AlgebraicGeometry/Stacks/FibreProductComparisonFiniteType.lean`, so that half is
one more application of the same longhand transfer and no part of Stacks 050I is withheld.

## References

* [Stacks Project, Tag 050I](https://stacks.math.columbia.edu/tag/050I)
* [Stacks Project, Tag 050H](https://stacks.math.columbia.edu/tag/050H)
* [Stacks Project, Tag 04T2](https://stacks.math.columbia.edu/tag/04T2)
* [Stacks Project, Tag 0457](https://stacks.math.columbia.edu/tag/0457)
* [Stacks Project, Tag 0459](https://stacks.math.columbia.edu/tag/0459)
* [Stacks Project, Tag 03YK](https://stacks.math.columbia.edu/tag/03YK)
* [Stacks Project, Tag 04XB](https://stacks.math.columbia.edu/tag/04XB)
* [Stacks Project, Tag 04YW](https://stacks.math.columbia.edu/tag/04YW)
-/

@[expose] public section

open CategoryTheory

namespace CategoryTheory.TwoFibreProductOver

universe v u v₁ u₁ v₂ u₂

variable {C : Type u} [Category.{v} C] {X : Type u₁} [Category.{v₁} X]
  {Y : Type u₂} [Category.{v₂} Y]

/-- **The 2-fibre product along an identity leg is the source.** The first projection
`X ×_{F, Y, 𝟭 Y} Y ⟶ X` is an equivalence, with inverse the tautological point
`CategoryTheory.TwoFibreProductOver.pointOfFunctor` of `F` taken at the identity leg: the counit
sends an object to its own comparison isomorphism, which is the only non-identity datum. -/
noncomputable def identityGraphEquivalence (pX : X ⥤ C) (pY : Y ⥤ C) (F : X ⥤ Y)
    (hF : F ⋙ pY = pX) :
    TwoFibreProductOver pX pY pY F (𝟭 Y) ≌ X := by
  let s := pointOfFunctor pX pY pY (𝟭 Y) rfl F hF
  let pr := fst pX pY pY F (𝟭 Y)
  have hCounit : pr ⋙ s ≅ 𝟭 (TwoFibreProductOver pX pY pY F (𝟭 Y)) := by
    let α : pr ⋙ s ⟶ 𝟭 (TwoFibreProductOver pX pY pY F (𝟭 Y)) := {
      app := fun Q => {
        hbase := eqToHom Q.hx
        a := 𝟙 Q.x
        b := Q.iso.hom
        ha := IsHomLift.id_lift_eqToHom_domain Q.hx rfl
        hb := by
          have hfx := congrArg (fun K : X ⥤ C => K.obj Q.x) hF
          change pY.obj (F.obj Q.x) = pX.obj Q.x at hfx
          apply IsHomLift.of_fac' pY (eqToHom Q.hx) Q.iso.hom hfx Q.hy
          let : pY.IsHomLift (𝟙 Q.base) Q.iso.hom := Q.vertical
          have hv := IsHomLift.fac' pY (𝟙 Q.base) Q.iso.hom
          have hdom : IsHomLift.domain_eq pY (𝟙 Q.base) Q.iso.hom = hfx.trans Q.hx :=
            Subsingleton.elim _ _
          have hcod : IsHomLift.codomain_eq pY (𝟙 Q.base) Q.iso.hom = Q.hy :=
            Subsingleton.elim _ _
          rw [hv, hdom, hcod]
          simp
        w := by
          change F.map (𝟙 Q.x) ≫ Q.iso.hom = (Iso.refl (F.obj Q.x)).hom ≫
            (𝟭 Y).map Q.iso.hom
          simp }
      naturality := by
        intro Q Q' φ
        apply Hom.ext'
        · change φ.a ≫ 𝟙 Q'.x = 𝟙 Q.x ≫ φ.a
          simp
        · exact φ.w }
    let hAppIso : ∀ Q : TwoFibreProductOver pX pY pY F (𝟭 Y),
        (pr ⋙ s).obj Q ≅ Q := fun Q => by
      let h : (pr ⋙ s).obj Q ⟶ Q := α.app Q
      let hi : Q ⟶ (pr ⋙ s).obj Q := {
        hbase := eqToHom Q.hx.symm
        a := 𝟙 Q.x
        b := Q.iso.inv
        ha := IsHomLift.id_lift_eqToHom_domain Q.hx.symm Q.hx
        hb := by
          have hfx := congrArg (fun K : X ⥤ C => K.obj Q.x) hF
          change pY.obj (F.obj Q.x) = pX.obj Q.x at hfx
          let : pY.IsHomLift (𝟙 Q.base) Q.iso.hom := Q.vertical
          let : pY.IsHomLift (𝟙 Q.base) Q.iso.inv := IsHomLift.lift_id_inv pY Q.base Q.iso
          apply IsHomLift.of_fac' pY (eqToHom Q.hx.symm) Q.iso.inv Q.hy hfx
          have hv := IsHomLift.fac' pY (𝟙 Q.base) Q.iso.inv
          have hdom : IsHomLift.domain_eq pY (𝟙 Q.base) Q.iso.inv = Q.hy :=
            Subsingleton.elim _ _
          have hcod : IsHomLift.codomain_eq pY (𝟙 Q.base) Q.iso.inv = hfx.trans Q.hx :=
            Subsingleton.elim _ _
          rw [hv, hdom, hcod]
          simp
        w := by
          change F.map (𝟙 Q.x) ≫ (Iso.refl (F.obj Q.x)).hom =
            Q.iso.hom ≫ (𝟭 Y).map Q.iso.inv
          simp }
      refine ⟨h, hi, ?_, ?_⟩
      · apply Hom.ext'
        · change 𝟙 Q.x ≫ 𝟙 Q.x = 𝟙 Q.x
          simp
        · change Q.iso.hom ≫ Q.iso.inv = 𝟙 (F.obj Q.x)
          exact Q.iso.hom_inv_id
      · apply Hom.ext'
        · change 𝟙 Q.x ≫ 𝟙 Q.x = 𝟙 Q.x
          simp
        · change Q.iso.inv ≫ Q.iso.hom = 𝟙 Q.y
          exact Q.iso.inv_hom_id
    exact NatIso.ofComponents hAppIso (by
      intro Q Q' φ
      simpa [hAppIso] using α.naturality φ)
  refine CategoryTheory.Equivalence.mk pr s hCounit.symm ?_
  exact NatIso.ofComponents (fun x => Iso.refl x) (by
    intro x y f
    change f ≫ 𝟙 y = 𝟙 x ≫ f
    calc
      f ≫ 𝟙 y = f := Category.comp_id f
      _ = 𝟙 x ≫ f := (Category.id_comp f).symm)

end CategoryTheory.TwoFibreProductOver

open CategoryTheory AlgebraicGeometry CategoryTheory.Bicategory

namespace AlgebraicGeometry.Stack

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {𝒳 𝒴 𝒯 : AlgebraicStacks.{u, w} B S hS}

/-- **The cone whose mediating 1-morphism is the graph.** For `g : 𝒳 ⟶ 𝒴` over `𝒯`, witnessed by
`η : p ≅ g ≫ q`, this is the 2-commutative square over the cospan `(p, q)` with apex `𝒳` and
projections `𝟙 𝒳` and `g`; the filler is `η` corrected by the left unitor. -/
def graphCone (g : 𝒳 ⟶ 𝒴) (p : 𝒳 ⟶ 𝒯) (q : 𝒴 ⟶ 𝒯) (η : p ≅ g ≫ q) :
    Bicategory.TwoCommSq p q :=
  { pt := 𝒳, fst := 𝟙 𝒳, snd := g, iso := (Bicategory.leftUnitor p).symm ≪≫ η }

/-- The natural isomorphism of underlying functors induced by `η : p ≅ g ≫ q`. Its components are
those of `η`, read through the two layers of the tower of induced bicategories. -/
noncomputable def graphBaseIso (g : 𝒳 ⟶ 𝒴) (p : 𝒳 ⟶ 𝒯) (q : 𝒴 ⟶ 𝒯) (η : p ≅ g ≫ q) :
    p.hom.hom.toFunctor ≅ (g ≫ q).hom.hom.toFunctor := by
  let a : NatTrans p.hom.hom.toFunctor (g ≫ q).hom.hom.toFunctor :=
    η.hom.hom.hom.toNatTrans
  let b : NatTrans (g ≫ q).hom.hom.toFunctor p.hom.hom.toFunctor :=
    η.inv.hom.hom.toNatTrans
  refine NatIso.ofComponents (fun x => ⟨a.app x, b.app x, ?_, ?_⟩) ?_
  · have hcomp := congrArg (fun z : p ⟶ p => z.hom.hom) η.hom_inv_id
    change (η.hom.hom.hom.comp η.inv.hom.hom) = BasedNatTrans.id p.hom.hom at hcomp
    have happ := congrArg (fun t : BasedNatTrans p.hom.hom p.hom.hom => t.toNatTrans.app x) hcomp
    rw [BasedNatTrans.comp_toNatTrans, NatTrans.vcomp_app,
      BasedNatTrans.id_toNatTrans] at happ
    convert happ using 1
    rfl
  · have hcomp := congrArg (fun z : (g ≫ q) ⟶ (g ≫ q) => z.hom.hom) η.inv_hom_id
    change (η.inv.hom.hom.comp η.hom.hom.hom) =
      BasedNatTrans.id (g ≫ q).hom.hom at hcomp
    have happ := congrArg (fun t : BasedNatTrans (g ≫ q).hom.hom (g ≫ q).hom.hom =>
      t.toNatTrans.app x) hcomp
    rw [BasedNatTrans.comp_toNatTrans, NatTrans.vcomp_app,
      BasedNatTrans.id_toNatTrans] at happ
    convert happ using 1
    rfl
  · intro x y f
    exact a.naturality f

/-- The components of `AlgebraicGeometry.Stack.graphBaseIso` are vertical over `𝒯`. -/
theorem isHomLift_graphBaseIso_hom_app (g : 𝒳 ⟶ 𝒴) (p : 𝒳 ⟶ 𝒯) (q : 𝒴 ⟶ 𝒯) (η : p ≅ g ≫ q)
    (x : 𝒳.val.val.obj) :
    𝒯.val.val.p.IsHomLift (𝟙 (𝒳.val.val.p.obj x))
      ((graphBaseIso B S hS g p q η).hom.app x) := by
  show 𝒯.val.val.p.IsHomLift (𝟙 (𝒳.val.val.p.obj x)) (η.hom.hom.hom.toNatTrans.app x)
  exact η.hom.hom.hom.isHomLift' x

/-- **The canonical cone morphism defining the graph**, including the two projection
2-isomorphisms and their compatibility with the 2-fibre-product square. It is a representative of
the unique morphism out of `AlgebraicGeometry.Stack.graphCone` supplied by the universal property
of Stacks 04T2. -/
noncomputable def graphMorphism (g : 𝒳 ⟶ 𝒴) (p : 𝒳 ⟶ 𝒯) (q : 𝒴 ⟶ 𝒯) (η : p ≅ g ≫ q) :
    Bicategory.TwoCommSq.PreHom (graphCone B S hS g p q η)
      (twoFibreProductSquareAlgebraicStacks B S hS p q) :=
  Quotient.out ((isTwoFibreProduct_twoFibreProductSquareAlgebraicStacks B S hS p q).from
    (graphCone B S hS g p q η))

/-- **The graph `Γ_g : 𝒳 ⟶ 𝒳 ×_𝒯 𝒴` of a 1-morphism over a base algebraic stack.** -/
noncomputable def graph (g : 𝒳 ⟶ 𝒴) (p : 𝒳 ⟶ 𝒯) (q : 𝒴 ⟶ 𝒯) (η : p ≅ g ≫ q) :
    𝒳 ⟶ twoFibreProductAlgebraicStack B S hS p q :=
  (graphMorphism B S hS g p q η).hom

/-- The first projection of the graph is 2-isomorphic to the identity. -/
noncomputable def graph_fst_iso (g : 𝒳 ⟶ 𝒴) (p : 𝒳 ⟶ 𝒯) (q : 𝒴 ⟶ 𝒯) (η : p ≅ g ≫ q) :
    (𝟙 𝒳) ≅ graph B S hS g p q η ≫
      (twoFibreProductSquareAlgebraicStacks B S hS p q).fst :=
  (graphMorphism B S hS g p q η).isoFst

/-- The second projection of the graph is 2-isomorphic to the given 1-morphism. -/
noncomputable def graph_snd_iso (g : 𝒳 ⟶ 𝒴) (p : 𝒳 ⟶ 𝒯) (q : 𝒴 ⟶ 𝒯) (η : p ≅ g ≫ q) :
    g ≅ graph B S hS g p q η ≫
      (twoFibreProductSquareAlgebraicStacks B S hS p q).snd :=
  (graphMorphism B S hS g p q η).isoSnd

/-! ### The two equivalences the comparison 1-morphism of Stacks 050H is corrected by -/

/-- The reindexing of the 2-fibre product along `η`, as a based functor: it turns the product
taken along `g ≫ q` into the one taken along `p`. -/
noncomputable def graphReindexBasedFunctor (g : 𝒳 ⟶ 𝒴) (p : 𝒳 ⟶ 𝒯) (q : 𝒴 ⟶ 𝒯)
    (η : p ≅ g ≫ q) :
    (twoFibreProductAlgebraicStack B S hS (g ≫ q) (𝟙 𝒴 ≫ q)).val.val ⥤ᵇ
      (twoFibreProductAlgebraicStack B S hS p q).val.val :=
  { toFunctor := TwoFibreProductOver.reindexSymm (G := q.hom.hom.toFunctor)
      (graphBaseIso B S hS g p q η) (isHomLift_graphBaseIso_hom_app B S hS g p q η)
    w := rfl }

/-- The reindexing of the 2-fibre product along `η⁻¹`, as a based functor: the inverse of
`AlgebraicGeometry.Stack.graphReindexBasedFunctor`. -/
noncomputable def graphReindexInvBasedFunctor (g : 𝒳 ⟶ 𝒴) (p : 𝒳 ⟶ 𝒯) (q : 𝒴 ⟶ 𝒯)
    (η : p ≅ g ≫ q) :
    (twoFibreProductAlgebraicStack B S hS p q).val.val ⥤ᵇ
      (twoFibreProductAlgebraicStack B S hS (g ≫ q) (𝟙 𝒴 ≫ q)).val.val :=
  { toFunctor := TwoFibreProductOver.reindex (G := q.hom.hom.toFunctor)
      (graphBaseIso B S hS g p q η) (isHomLift_graphBaseIso_hom_app B S hS g p q η)
    w := rfl }

/-- The two reindexing based functors compose to the identity. -/
theorem graphReindex_comp_graphReindexInv (g : 𝒳 ⟶ 𝒴) (p : 𝒳 ⟶ 𝒯) (q : 𝒴 ⟶ 𝒯)
    (η : p ≅ g ≫ q) :
    BasedFunctor.comp (graphReindexBasedFunctor B S hS g p q η)
        (graphReindexInvBasedFunctor B S hS g p q η) =
      BasedFunctor.id (twoFibreProductAlgebraicStack B S hS (g ≫ q) (𝟙 𝒴 ≫ q)).val.val := by
  apply BasedCategory.BasedFunctor.ext'
  exact TwoFibreProductOver.reindexSymm_comp_reindex (G := q.hom.hom.toFunctor)
    (graphBaseIso B S hS g p q η) (isHomLift_graphBaseIso_hom_app B S hS g p q η)

/-- The reindexing 1-morphism of 2-fibre products of algebraic stacks attached to `η`. -/
noncomputable def graphReindexMap (g : 𝒳 ⟶ 𝒴) (p : 𝒳 ⟶ 𝒯) (q : 𝒴 ⟶ 𝒯) (η : p ≅ g ≫ q) :
    twoFibreProductAlgebraicStack B S hS (g ≫ q) (𝟙 𝒴 ≫ q) ⟶
      twoFibreProductAlgebraicStack B S hS p q :=
  Bicategory.InducedBicategory.mkHom
    (Bicategory.InducedBicategory.mkHom (graphReindexBasedFunctor B S hS g p q η))

/-- The based functor identifying `𝒳` with the 2-fibre product `𝒳 ×_{g, 𝒴, 𝟙 𝒴} 𝒴`. -/
def graphIdentitySectionBasedFunctor (g : 𝒳 ⟶ 𝒴) :
    𝒳.val.val ⥤ᵇ (twoFibreProductAlgebraicStack B S hS g (𝟙 𝒴)).val.val :=
  { toFunctor := by
      change 𝒳.val.val.obj ⥤
        TwoFibreProductOver 𝒳.val.val.p 𝒴.val.val.p 𝒴.val.val.p
          g.hom.hom.toFunctor (𝟭 𝒴.val.val.obj)
      exact TwoFibreProductOver.pointOfFunctor 𝒳.val.val.p 𝒴.val.val.p 𝒴.val.val.p
        (𝟭 𝒴.val.val.obj) rfl g.hom.hom.toFunctor g.hom.hom.w
    w := rfl }

/-- The 1-morphism `𝒳 ⟶ 𝒳 ×_{g, 𝒴, 𝟙 𝒴} 𝒴` identifying the source with the 2-fibre product
along an identity leg. -/
def graphIdentitySection (g : 𝒳 ⟶ 𝒴) :
    𝒳 ⟶ twoFibreProductAlgebraicStack B S hS g (𝟙 𝒴) :=
  Bicategory.InducedBicategory.mkHom
    (Bicategory.InducedBicategory.mkHom (graphIdentitySectionBasedFunctor B S hS g))

/-- `AlgebraicGeometry.Stack.graphIdentitySection` is an equivalence on underlying categories. -/
theorem graphIdentitySection_isEquivalence (g : 𝒳 ⟶ 𝒴) :
    Functor.IsEquivalence (graphIdentitySection B S hS g).hom.hom.toFunctor := by
  show Functor.IsEquivalence (TwoFibreProductOver.pointOfFunctor 𝒳.val.val.p 𝒴.val.val.p
    𝒴.val.val.p (𝟭 𝒴.val.val.obj) rfl g.hom.hom.toFunctor g.hom.hom.w)
  exact (TwoFibreProductOver.identityGraphEquivalence 𝒳.val.val.p 𝒴.val.val.p
    g.hom.hom.toFunctor g.hom.hom.w).isEquivalence_inverse

/-- `AlgebraicGeometry.Stack.graphReindexMap` is an equivalence on underlying categories. -/
theorem graphReindexMap_isEquivalence (g : 𝒳 ⟶ 𝒴) (p : 𝒳 ⟶ 𝒯) (q : 𝒴 ⟶ 𝒯) (η : p ≅ g ≫ q) :
    Functor.IsEquivalence (graphReindexMap B S hS g p q η).hom.hom.toFunctor :=
  TwoFibreProductOver.reindexSymm_isEquivalence (G := q.hom.hom.toFunctor)
    (graphBaseIso B S hS g p q η) (isHomLift_graphBaseIso_hom_app B S hS g p q η)

/-- `AlgebraicGeometry.Stack.graphReindexInvBasedFunctor` is an equivalence on underlying
categories. -/
theorem graphReindexInvBasedFunctor_isEquivalence (g : 𝒳 ⟶ 𝒴) (p : 𝒳 ⟶ 𝒯) (q : 𝒴 ⟶ 𝒯)
    (η : p ≅ g ≫ q) :
    Functor.IsEquivalence (graphReindexInvBasedFunctor B S hS g p q η).toFunctor :=
  TwoFibreProductOver.isEquivalence_reindex (G := q.hom.hom.toFunctor)
    (graphBaseIso B S hS g p q η) (isHomLift_graphBaseIso_hom_app B S hS g p q η)

/-! ### The graph as the comparison 1-morphism corrected by those two equivalences -/

/-- The composite `𝒳 ⟶ 𝒳 ×_𝒴 𝒴 ⟶ 𝒳 ×_𝒯 𝒴 ⟶ 𝒳 ×_{p, 𝒯, q} 𝒴` of the identity-leg section, the
comparison 1-morphism of Stacks 050H and the reindexing along `η`. -/
noncomputable def graphComparisonComposite (g : 𝒳 ⟶ 𝒴) (p : 𝒳 ⟶ 𝒯) (q : 𝒴 ⟶ 𝒯)
    (η : p ≅ g ≫ q) : 𝒳 ⟶ twoFibreProductAlgebraicStack B S hS p q :=
  graphIdentitySection B S hS g ≫
    comparison B S hS g (𝟙 𝒴) q ≫ graphReindexMap B S hS g p q η

/-- A 2-isomorphism of 1-morphisms of categories fibred in groupoids, read as a natural
isomorphism of the underlying functors. -/
def cfgIsoToNatIso {C : Type*} [Category C] {𝒳 𝒴 : CatFiberedInGroupoids C} {F G : 𝒳 ⟶ 𝒴}
    (e : F ≅ G) : F.hom.toFunctor ≅ G.hom.toFunctor where
  hom := e.hom.hom.toNatTrans
  inv := e.inv.hom.toNatTrans
  hom_inv_id := congrArg (fun α => α.hom.toNatTrans) e.hom_inv_id
  inv_hom_id := congrArg (fun α => α.hom.toNatTrans) e.inv_hom_id

/-- The underlying functor of the graph is 2-isomorphic to the mediating functor
`CategoryTheory.TwoFibreProductOver.lift` of the cone `(𝟭, g, η)`. This is the uniqueness half of
the 2-universal property of Stacks 0040 applied to the representative
`AlgebraicGeometry.Stack.graphMorphism`. -/
noncomputable def graphUnderlyingLiftIso (g : 𝒳 ⟶ 𝒴) (p : 𝒳 ⟶ 𝒯) (q : 𝒴 ⟶ 𝒯)
    (η : p ≅ g ≫ q) :
    (graphMorphism B S hS g p q η).hom.hom.hom.toFunctor ≅
      TwoFibreProductOver.lift 𝒳.val.val.p 𝒴.val.val.p 𝒯.val.val.p
        p.hom.hom.toFunctor q.hom.hom.toFunctor 𝒳.val.val.p
        (Functor.id (C := 𝒳.val.val.obj)) g.hom.hom.toFunctor (by rfl)
        g.hom.hom.w (graphBaseIso B S hS g p q η)
        (isHomLift_graphBaseIso_hom_app B S hS g p q η) := by
  let m := graphMorphism B S hS g p q η
  let C := graphCone B S hS g p q η
  let R := C.underlying
  let r : Bicategory.TwoCommSq.PreHom R
      (twoFibreProductSquareAlgebraicStacks B S hS p q).underlying := m.underlying
  let γ := r.hom.hom.toFunctor
  let F := p.hom.hom.toFunctor
  let G := q.hom.hom.toFunctor
  let a := cfgIsoToNatIso r.isoFst.symm
  let b := cfgIsoToNatIso r.isoSnd.symm
  let t := cfgIsoToNatIso R.iso
  let ψ := TwoFibreProductOver.psiIso 𝒳.val.val.p 𝒴.val.val.p 𝒯.val.val.p F G
  apply TwoFibreProductOver.liftIso γ a b
  · intro x
    change 𝒳.val.val.p.IsHomLift (𝟙 (𝒳.val.val.p.obj x))
      (r.isoFst.symm.hom.hom.toNatTrans.app x)
    exact r.isoFst.symm.hom.hom.isHomLift' x
  · intro x
    change 𝒴.val.val.p.IsHomLift (𝟙 (𝒳.val.val.p.obj x))
      (r.isoSnd.symm.hom.hom.toNatTrans.app x)
    exact r.isoSnd.symm.hom.hom.isHomLift' x
  · have hab : Functor.whiskerRight a.hom F ≫ t.hom =
        Functor.whiskerLeft γ ψ.hom ≫ Functor.whiskerRight b.hom G := by
      ext x
      have h0 : t.hom.app x ≫ q.hom.hom.toFunctor.map (b.inv.app x) ≫ 𝟙 _ =
          p.hom.hom.toFunctor.map (a.inv.app x) ≫ 𝟙 _ ≫ (γ.obj x).iso.hom :=
        congrArg (fun α => α.hom.toNatTrans.app x) r.compat
      have h : t.hom.app x ≫ q.hom.hom.toFunctor.map (b.inv.app x) =
          p.hom.hom.toFunctor.map (a.inv.app x) ≫ (γ.obj x).iso.hom :=
        ((congrArg (fun z => t.hom.app x ≫ z) (Category.comp_id _).symm).trans h0).trans
          (congrArg (fun z => p.hom.hom.toFunctor.map (a.inv.app x) ≫ z)
            (Category.id_comp _))
      change p.hom.hom.toFunctor.map (a.hom.app x) ≫ t.hom.app x =
        (γ.obj x).iso.hom ≫ q.hom.hom.toFunctor.map (b.hom.app x)
      have hb : q.hom.hom.toFunctor.map (b.inv.app x) ≫
          q.hom.hom.toFunctor.map (b.hom.app x) = 𝟙 _ :=
        (q.hom.hom.toFunctor.map_comp _ _).symm.trans
          ((congrArg q.hom.hom.toFunctor.map (b.inv_hom_id_app x)).trans
            (q.hom.hom.toFunctor.map_id _))
      have ha : p.hom.hom.toFunctor.map (a.hom.app x) ≫
          p.hom.hom.toFunctor.map (a.inv.app x) = 𝟙 _ :=
        (p.hom.hom.toFunctor.map_comp _ _).symm.trans
          ((congrArg p.hom.hom.toFunctor.map (a.hom_inv_id_app x)).trans
            (p.hom.hom.toFunctor.map_id _))
      exact (congrArg (fun z => p.hom.hom.toFunctor.map (a.hom.app x) ≫ z)
          ((Category.comp_id (t.hom.app x)).symm.trans
            (congrArg (fun z => t.hom.app x ≫ z) hb.symm))).trans
        ((congrArg (fun z => p.hom.hom.toFunctor.map (a.hom.app x) ≫ z)
            ((Category.assoc (t.hom.app x) (q.hom.hom.toFunctor.map (b.inv.app x))
                (q.hom.hom.toFunctor.map (b.hom.app x))).symm.trans
              ((congrArg (fun z => z ≫ q.hom.hom.toFunctor.map (b.hom.app x)) h).trans
                (Category.assoc (p.hom.hom.toFunctor.map (a.inv.app x)) ((γ.obj x).iso.hom)
                  (q.hom.hom.toFunctor.map (b.hom.app x)))))).trans
          ((Category.assoc (p.hom.hom.toFunctor.map (a.hom.app x))
              (p.hom.hom.toFunctor.map (a.inv.app x))
              ((γ.obj x).iso.hom ≫ q.hom.hom.toFunctor.map (b.hom.app x))).symm.trans
            ((congrArg (fun z => z ≫ (γ.obj x).iso.hom ≫
                q.hom.hom.toFunctor.map (b.hom.app x)) ha).trans
              (Category.id_comp ((γ.obj x).iso.hom ≫
                q.hom.hom.toFunctor.map (b.hom.app x))))))
    have ht : t.hom = (graphBaseIso B S hS g p q η).hom := by
      ext x
      simp only [t, cfgIsoToNatIso, R, C, Bicategory.TwoCommSq.underlying,
        graphBaseIso, graphCone, Bicategory.InducedBicategory.isoMk,
        Bicategory.leftUnitor, BasedNatIso.id,
        Bicategory.InducedBicategory.categoryStruct_comp_hom,
        BasedCategory.comp_def]
      change (BasedNatTrans.comp (BasedNatTrans.id p.hom.hom) η.hom.hom.hom).toNatTrans.app x =
        η.hom.hom.hom.toNatTrans.app x
      simp only [BasedNatTrans.comp, BasedNatTrans.id]
      exact (NatTrans.comp_app _ _ x).trans (Category.id_comp _)
    rw [ht] at hab
    exact hab

/-- The underlying functor of `AlgebraicGeometry.Stack.graphComparisonComposite` is 2-isomorphic
to the same mediating functor as the graph: its value at an object differs from the mediating
one's only by a composition with an identity. -/
noncomputable def graphComparisonCompositeLiftIso (g : 𝒳 ⟶ 𝒴) (p : 𝒳 ⟶ 𝒯) (q : 𝒴 ⟶ 𝒯)
    (η : p ≅ g ≫ q) :
    (graphComparisonComposite B S hS g p q η).hom.hom.toFunctor ≅
      TwoFibreProductOver.lift 𝒳.val.val.p 𝒴.val.val.p 𝒯.val.val.p
        p.hom.hom.toFunctor q.hom.hom.toFunctor 𝒳.val.val.p
        (Functor.id (C := 𝒳.val.val.obj)) g.hom.hom.toFunctor (by rfl)
        g.hom.hom.w (graphBaseIso B S hS g p q η)
        (isHomLift_graphBaseIso_hom_app B S hS g p q η) := by
  let H := (graphComparisonComposite B S hS g p q η).hom.hom.toFunctor
  let L := TwoFibreProductOver.lift 𝒳.val.val.p 𝒴.val.val.p 𝒯.val.val.p
    p.hom.hom.toFunctor q.hom.hom.toFunctor 𝒳.val.val.p
    (Functor.id (C := 𝒳.val.val.obj)) g.hom.hom.toFunctor (by rfl)
    g.hom.hom.w (graphBaseIso B S hS g p q η)
    (isHomLift_graphBaseIso_hom_app B S hS g p q η)
  have hobj : ∀ x, H.obj x = L.obj x := by
    intro x
    apply TwoFibreProductOver.obj_ext
    apply Iso.ext
    change (graphBaseIso B S hS g p q η).hom.app x ≫
      q.hom.hom.toFunctor.map (𝟙 (g.hom.hom.toFunctor.obj x)) =
        (graphBaseIso B S hS g p q η).hom.app x
    rw [q.hom.hom.toFunctor.map_id]
    exact Category.comp_id _
  refine NatIso.ofComponents (fun x => eqToIso (hobj x)) ?_
  intro x y f
  apply TwoFibreProductOver.Hom.ext'
  · change f ≫ (eqToHom (hobj y)).a = (eqToHom (hobj x)).a ≫ f
    have hx : (eqToHom (hobj x)).a = 𝟙 x := TwoFibreProductOver.Hom.a_eqToHom _
    have hy : (eqToHom (hobj y)).a = 𝟙 y := TwoFibreProductOver.Hom.a_eqToHom _
    exact (congrArg (f ≫ ·) hy).trans ((Category.comp_id f).trans
      ((Category.id_comp f).symm.trans (congrArg (· ≫ f) hx.symm)))
  · change g.hom.hom.map f ≫ (eqToHom (hobj y)).b =
      (eqToHom (hobj x)).b ≫ g.hom.hom.map f
    have hx : (eqToHom (hobj x)).b = 𝟙 (g.hom.hom.obj x) := TwoFibreProductOver.Hom.b_eqToHom _
    have hy : (eqToHom (hobj y)).b = 𝟙 (g.hom.hom.obj y) := TwoFibreProductOver.Hom.b_eqToHom _
    exact (congrArg (g.hom.hom.map f ≫ ·) hy).trans
      ((Category.comp_id _).trans ((Category.id_comp _).symm.trans
        (congrArg (· ≫ g.hom.hom.map f) hx.symm)))

/-- The graph and `AlgebraicGeometry.Stack.graphComparisonComposite` have 2-isomorphic underlying
functors: both are mediating functors of the same cone. -/
noncomputable def graphComparisonCompositeIso (g : 𝒳 ⟶ 𝒴) (p : 𝒳 ⟶ 𝒯) (q : 𝒴 ⟶ 𝒯)
    (η : p ≅ g ≫ q) :
    (graph B S hS g p q η).hom.hom.toFunctor ≅
      (graphComparisonComposite B S hS g p q η).hom.hom.toFunctor :=
  (graphUnderlyingLiftIso B S hS g p q η).trans
    (graphComparisonCompositeLiftIso B S hS g p q η).symm

/-- `AlgebraicGeometry.Stack.graphComparisonCompositeIso` is a 2-isomorphism over the site: its
components are vertical, because they agree with those of the first comparison 2-isomorphism of
`AlgebraicGeometry.Stack.graphMorphism`. -/
noncomputable def graphComparisonCompositeBasedIso (g : 𝒳 ⟶ 𝒴) (p : 𝒳 ⟶ 𝒯) (q : 𝒴 ⟶ 𝒯)
    (η : p ≅ g ≫ q) :
    (graph B S hS g p q η).hom.hom ≅ (graphComparisonComposite B S hS g p q η).hom.hom := by
  apply BasedNatIso.mkNatIso (graphComparisonCompositeIso B S hS g p q η)
  intro x
  apply ((twoFibreProductSquareAlgebraicStacks B S hS p q).fst.hom.hom.isHomLift_iff
    (𝟙 (𝒳.val.val.p.obj x)) _).mp
  have ha : ((graphComparisonCompositeLiftIso B S hS g p q η).inv.app x).a = 𝟙 x := by
    dsimp only [graphComparisonCompositeLiftIso, NatIso.ofComponents, eqToIso]
    exact TwoFibreProductOver.Hom.a_eqToHom _
  change 𝒳.val.val.p.IsHomLift (𝟙 (𝒳.val.val.p.obj x))
    (((graphUnderlyingLiftIso B S hS g p q η).hom.app x).a ≫
      ((graphComparisonCompositeLiftIso B S hS g p q η).inv.app x).a)
  have he : ((graphUnderlyingLiftIso B S hS g p q η).hom.app x).a ≫
      ((graphComparisonCompositeLiftIso B S hS g p q η).inv.app x).a =
      (graphMorphism B S hS g p q η).isoFst.inv.hom.hom.toNatTrans.app x :=
    (congrArg (((graphUnderlyingLiftIso B S hS g p q η).hom.app x).a ≫ ·) ha).trans
      (Category.comp_id _)
  exact he.symm ▸ (graphMorphism B S hS g p q η).isoFst.inv.hom.hom.isHomLift' x

/-! ### Stacks 050I, the two assertions this library can state -/

/-- The identity based functor is an equivalence on underlying categories. -/
private theorem isEquivalence_basedFunctor_id {𝒮 : Type*} [Category 𝒮] (𝒳 : BasedCategory 𝒮) :
    Functor.IsEquivalence (BasedFunctor.id 𝒳).toFunctor :=
  Functor.isEquivalence_refl

/-- **Stacks 050I, part (1), representability half.** The graph of a 1-morphism of algebraic
stacks over a base algebraic stack is representable by algebraic spaces.

The graph is 2-isomorphic to the comparison 1-morphism of Stacks 050H precomposed and
postcomposed with equivalences, and representability by algebraic spaces is invariant under such
a square by Stacks 0457. -/
@[stacks 050I "part (1): representable by algebraic spaces"]
theorem isRepresentableByAlgebraicSpaces_graph (g : 𝒳 ⟶ 𝒴) (p : 𝒳 ⟶ 𝒯) (q : 𝒴 ⟶ 𝒯)
    (η : p ≅ g ≫ q) :
    IsRepresentableByAlgebraicSpaces B S hS (graph B S hS g p q η).hom.hom := by
  let a := graphIdentitySection B S hS g
  let c := comparison B S hS g (𝟙 𝒴) q
  let b := graphReindexMap B S hS g p q η
  let m := c ≫ b
  let idSource : twoFibreProductAlgebraicStack B S hS g (𝟙 𝒴) ⟶
      twoFibreProductAlgebraicStack B S hS g (𝟙 𝒴) := 𝟙 _
  let idTarget : twoFibreProductAlgebraicStack B S hS p q ⟶
      twoFibreProductAlgebraicStack B S hS p q := 𝟙 _
  let : Functor.IsEquivalence idSource.hom.hom.toFunctor := isEquivalence_basedFunctor_id _
  let : Functor.IsEquivalence idTarget.hom.hom.toFunctor := isEquivalence_basedFunctor_id _
  let : Functor.IsEquivalence a.hom.hom.toFunctor :=
    graphIdentitySection_isEquivalence B S hS g
  let : Functor.IsEquivalence b.hom.hom.toFunctor :=
    graphReindexMap_isEquivalence B S hS g p q η
  have hrepM : IsRepresentableByAlgebraicSpaces B S hS m.hom.hom := by
    have he := isRepresentableByAlgebraicSpaces_iff_of_equivalences B S hS
      c.hom.hom m.hom.hom idSource.hom.hom b.hom.hom (Iso.refl _)
    exact he.mpr (isRepresentableByAlgebraicSpaces_comparison B S hS g (𝟙 𝒴) q)
  have he := isRepresentableByAlgebraicSpaces_iff_of_equivalences B S hS
    (graph B S hS g p q η).hom.hom m.hom.hom a.hom.hom idTarget.hom.hom
    (graphComparisonCompositeBasedIso B S hS g p q η).symm
  exact he.mp hrepM

/-- **Any relative property of the comparison 1-morphism of Stacks 050H transfers to the graph,
with no hypothesis on the property.** The property is written out as the quantifier of
Stacks 03YK, which is the form the conditions of Stacks 04YW and the properties of Properties of
Stacks, Section 04XB are stated with.

Stacks 0459 at the two equivalences of `AlgebraicGeometry.Stack.graphComparisonComposite`, in two
steps: first from the comparison to its composite with the reindexing — where the comparison
square commutes because the two reindexing functors compose to the identity, so its 2-cell is an
`CategoryTheory.eqToIso` — and then from that composite to the graph. Both steps are
`AlgebraicGeometry.Stack.relativeProperty_of_equivalences`, which needs neither stability under
base change nor locality at the target. -/
theorem relativeProperty_graph_of_comparison (P : MorphismProperty (AlgebraicSpaces B S hS))
    (g : 𝒳 ⟶ 𝒴) (p : 𝒳 ⟶ 𝒯) (q : 𝒴 ⟶ 𝒯) (η : p ≅ g ≫ q)
    (hcmp : ∀ (U : BigFppfOver B S hS)
      (y : BigFppfOver B U.left.1 U.left.2 ⥤
        (twoFibreProductAlgebraicStack B S hS (g ≫ q) (𝟙 𝒴 ≫ q)).val.val.obj)
      (_hy : y ⋙ (twoFibreProductAlgebraicStack B S hS (g ≫ q) (𝟙 𝒴 ≫ q)).val.val.p =
        Over.map U.hom)
      (F : (BigFppfOver B U.left.1 U.left.2)ᵒᵖ ⥤ Type u)
      (hF : IsAlgebraicSpace B U.left.1 U.left.2 F),
      Nonempty (StacksRepresentableCFG.EquivalenceOver
        (TwoFibreProductOver.fst (Over.map U.hom)
          (twoFibreProductAlgebraicStack B S hS g (𝟙 𝒴)).val.val.p
          (twoFibreProductAlgebraicStack B S hS (g ≫ q) (𝟙 𝒴 ≫ q)).val.val.p y
          (comparison B S hS g (𝟙 𝒴) q).hom.hom.toFunctor)
        (presheafOfCategories (F ⋙ typeToCat)).p) →
      P (algebraicSpaceMap B S hS U
        ((spacesOverSmallerBaseFunctor B U.left.1 S U.left.2 hS U.hom).obj ⟨F, hF⟩))) :
    ∀ (U : BigFppfOver B S hS)
      (y : BigFppfOver B U.left.1 U.left.2 ⥤
        (twoFibreProductAlgebraicStack B S hS p q).val.val.obj)
      (_hy : y ⋙ (twoFibreProductAlgebraicStack B S hS p q).val.val.p = Over.map U.hom)
      (F : (BigFppfOver B U.left.1 U.left.2)ᵒᵖ ⥤ Type u)
      (hF : IsAlgebraicSpace B U.left.1 U.left.2 F),
      Nonempty (StacksRepresentableCFG.EquivalenceOver
        (TwoFibreProductOver.fst (Over.map U.hom) 𝒳.val.val.p
          (twoFibreProductAlgebraicStack B S hS p q).val.val.p y
          (graph B S hS g p q η).hom.hom.toFunctor)
        (presheafOfCategories (F ⋙ typeToCat)).p) →
      P (algebraicSpaceMap B S hS U
        ((spacesOverSmallerBaseFunctor B U.left.1 S U.left.2 hS U.hom).obj ⟨F, hF⟩)) := by
  let : Functor.IsEquivalence (graphIdentitySection B S hS g).hom.hom.toFunctor :=
    graphIdentitySection_isEquivalence B S hS g
  let : Functor.IsEquivalence (graphReindexMap B S hS g p q η).hom.hom.toFunctor :=
    graphReindexMap_isEquivalence B S hS g p q η
  let : Functor.IsEquivalence (graphReindexInvBasedFunctor B S hS g p q η).toFunctor :=
    graphReindexInvBasedFunctor_isEquivalence B S hS g p q η
  let : Functor.IsEquivalence
      (BasedFunctor.id (twoFibreProductAlgebraicStack B S hS p q).val.val).toFunctor :=
    isEquivalence_basedFunctor_id _
  let : Functor.IsEquivalence
      (BasedFunctor.id (twoFibreProductAlgebraicStack B S hS g (𝟙 𝒴)).val.val).toFunctor :=
    isEquivalence_basedFunctor_id _
  refine relativeProperty_of_equivalences B S hS P (graph B S hS g p q η).hom.hom
    (comparison B S hS g (𝟙 𝒴) q ≫ graphReindexMap B S hS g p q η).hom.hom
    (graphIdentitySection B S hS g).hom.hom
    (BasedFunctor.id (twoFibreProductAlgebraicStack B S hS p q).val.val)
    (graphComparisonCompositeBasedIso B S hS g p q η).symm ?_
  refine relativeProperty_of_equivalences B S hS P
    (comparison B S hS g (𝟙 𝒴) q ≫ graphReindexMap B S hS g p q η).hom.hom
    (comparison B S hS g (𝟙 𝒴) q).hom.hom
    (BasedFunctor.id (twoFibreProductAlgebraicStack B S hS g (𝟙 𝒴)).val.val)
    (graphReindexInvBasedFunctor B S hS g p q η) (eqToIso ?_) hcmp
  apply BasedCategory.BasedFunctor.ext'
  exact congrArg (fun K => (comparison B S hS g (𝟙 𝒴) q).hom.hom.toFunctor ⋙ K)
    (TwoFibreProductOver.reindexSymm_comp_reindex (p𝒴 := 𝒴.val.val.p)
      (G := q.hom.hom.toFunctor) (graphBaseIso B S hS g p q η)
      (isHomLift_graphBaseIso_hom_app B S hS g p q η)).symm

/-- **Any relative property of the comparison 1-morphism of Stacks 050H transfers to the
graph.** `AlgebraicGeometry.Stack.relativeProperty_graph_of_comparison` stated through the
abbreviation `AlgebraicGeometry.Stack.HasRelativeProperty` of Stacks 03YK. The two instance
hypotheses of that abbreviation are not used by the argument; they are in scope because the
statement mentions it. -/
theorem hasRelativeProperty_graph_of_comparison (P : MorphismProperty (AlgebraicSpaces B S hS))
    [P.IsStableUnderBaseChange] [P.IsLocalAtTarget (Space.Topology.fppf.precoverage B S hS)]
    (g : 𝒳 ⟶ 𝒴) (p : 𝒳 ⟶ 𝒯) (q : 𝒴 ⟶ 𝒯) (η : p ≅ g ≫ q)
    (hcmp : HasRelativeProperty B S hS P (comparison B S hS g (𝟙 𝒴) q).hom
      (isRepresentableByAlgebraicSpaces_comparison B S hS g (𝟙 𝒴) q)) :
    HasRelativeProperty B S hS P (graph B S hS g p q η).hom
      (isRepresentableByAlgebraicSpaces_graph B S hS g p q η) :=
  relativeProperty_graph_of_comparison B S hS P g p q η hcmp

/-- **Stacks 050I, part (2).** If `q : 𝒴 ⟶ 𝒯` is Deligne–Mumford then the graph of `g : 𝒳 ⟶ 𝒴`
over `𝒯` is unramified, in the relative sense of Stacks 03YK.

By Stacks 050H part (4) the comparison 1-morphism `𝒳 ×_𝒴 𝒴 ⟶ 𝒳 ×_𝒯 𝒴` is unramified, and
`AlgebraicGeometry.Stack.hasRelativeProperty_graph_of_comparison` carries that to the graph. The
two instance arguments of Stacks 03YK are Stacks 03ZJ and Stacks 042A composed with the
comparison of the fppf and fpqc precoverages. -/
@[stacks 050I "part (2)"]
theorem isUnramified_graph (g : 𝒳 ⟶ 𝒴) (p : 𝒳 ⟶ 𝒯) (q : 𝒴 ⟶ 𝒯) (η : p ≅ g ≫ q)
    (hq : IsDM B S hS q) :
    letI : MorphismProperty.IsStableUnderBaseChange
      (fun ⦃X Y : AlgebraicSpaces B S hS⦄ (k : X ⟶ Y) =>
        Space.IsUnramified B S hS k.hom) :=
      Space.isUnramified_isStableUnderBaseChange B S hS
    letI : MorphismProperty.IsLocalAtTarget
      (fun ⦃X Y : AlgebraicSpaces B S hS⦄ (k : X ⟶ Y) =>
        Space.IsUnramified B S hS k.hom)
      (Space.Topology.fppf.precoverage.{u, u} B S hS) :=
      (Space.isUnramified_isLocalAtTarget_fpqc B S hS).of_le
        (Space.fppfPrecoverage_le_fpqcPrecoverage.{u, u} B S hS)
    HasRelativeProperty B S hS
      (fun _ _ k => Space.IsUnramified B S hS k.hom)
      (graph B S hS g p q η).hom
      (isRepresentableByAlgebraicSpaces_graph B S hS g p q η) := by
  let := Space.isUnramified_isStableUnderBaseChange B S hS
  let := (Space.isUnramified_isLocalAtTarget_fpqc B S hS).of_le
    (Space.fppfPrecoverage_le_fpqcPrecoverage.{u, u} B S hS)
  exact hasRelativeProperty_graph_of_comparison B S hS _ g p q η
    (isUnramified_comparison B S hS g (𝟙 𝒴) q hq)

/-- **Stacks 050I, part (1), locally-of-finite-type half.** The graph of a 1-morphism of
algebraic stacks over a base algebraic stack is locally of finite type, in the sense of
Properties of Stacks, Section 04XB.

By the locally-of-finite-type half of Stacks 050H part (1) the comparison 1-morphism
`𝒳 ×_𝒴 𝒴 ⟶ 𝒳 ×_𝒯 𝒴` is locally of finite type, and
`AlgebraicGeometry.Stack.relativeProperty_graph_of_comparison` carries that to the graph. No
hypothesis on `q` is needed, exactly as in Stacks 050H. Together with
`AlgebraicGeometry.Stack.isRepresentableByAlgebraicSpaces_graph` this is the whole of part (1). -/
@[stacks 050I "part (1): locally of finite type"]
theorem isLocallyOfFiniteType_graph (g : 𝒳 ⟶ 𝒴) (p : 𝒳 ⟶ 𝒯) (q : 𝒴 ⟶ 𝒯) (η : p ≅ g ≫ q) :
    IsLocallyOfFiniteType B S hS (graph B S hS g p q η).hom :=
  relativeProperty_graph_of_comparison B S hS
    (fun _ _ k => Space.IsLocallyOfFiniteType B S hS k.hom) g p q η
    (isLocallyOfFiniteType_comparison B S hS g (𝟙 𝒴) q)

/-- **Stacks 050I, part (3).** If `q : 𝒴 ⟶ 𝒯` is quasi-DM then the graph of `g : 𝒳 ⟶ 𝒴` over `𝒯`
is locally quasi-finite, in the sense of Properties of Stacks, Section 04XB.

By Stacks 050H part (5) the comparison 1-morphism `𝒳 ×_𝒴 𝒴 ⟶ 𝒳 ×_𝒯 𝒴` is locally quasi-finite,
and `AlgebraicGeometry.Stack.relativeProperty_graph_of_comparison` carries that to the graph.
One statement suffices: Stacks 050H takes the quasi-DM condition of Stacks 04YW apart, so the
input is local quasi-finiteness alone. -/
@[stacks 050I "part (3)"]
theorem isLocallyQuasiFinite_graph (g : 𝒳 ⟶ 𝒴) (p : 𝒳 ⟶ 𝒯) (q : 𝒴 ⟶ 𝒯) (η : p ≅ g ≫ q)
    (hq : AlgebraicStacks.IsQuasiDM B S hS q) :
    IsLocallyQuasiFinite B S hS (graph B S hS g p q η).hom :=
  relativeProperty_graph_of_comparison B S hS
    (fun _ _ k => Space.IsLocallyQuasiFinite B S hS k.hom) g p q η
    (isLocallyQuasiFinite_comparison B S hS g (𝟙 𝒴) q hq)

/-- **Stacks 050I, part (4).** If `q : 𝒴 ⟶ 𝒯` is separated then the graph of `g : 𝒳 ⟶ 𝒴` over
`𝒯` is proper, in the sense of Properties of Stacks, Section 04XB.

By Stacks 050H part (6) the comparison 1-morphism `𝒳 ×_𝒴 𝒴 ⟶ 𝒳 ×_𝒯 𝒴` is proper, and
`AlgebraicGeometry.Stack.relativeProperty_graph_of_comparison` carries that to the graph. The
separatedness condition of Stacks 04YW is a single property of the relative diagonal, so there
is no conjunction to project here. -/
@[stacks 050I "part (4)"]
theorem isProper_graph (g : 𝒳 ⟶ 𝒴) (p : 𝒳 ⟶ 𝒯) (q : 𝒴 ⟶ 𝒯) (η : p ≅ g ≫ q)
    (hq : AlgebraicStacks.IsSeparated B S hS q) :
    IsProper B S hS (graph B S hS g p q η).hom :=
  relativeProperty_graph_of_comparison B S hS
    (fun _ _ k => Space.IsProper B S hS k.hom) g p q η
    (isProper_comparison B S hS g (𝟙 𝒴) q hq)

/-- **Stacks 050I, part (5), the quasi-compactness half.** If `q : 𝒴 ⟶ 𝒯` is quasi-separated
then the graph of `g : 𝒳 ⟶ 𝒴` over `𝒯` is quasi-compact, in the sense of Properties of Stacks,
Section 04XB.

By Stacks 050H part (7) the comparison 1-morphism `𝒳 ×_𝒴 𝒴 ⟶ 𝒳 ×_𝒯 𝒴` is quasi-compact, and
`AlgebraicGeometry.Stack.relativeProperty_graph_of_comparison` carries that to the graph. A
single statement suffices here, because Stacks 050H already projects the conjunction of
Stacks 04YW quasi-separatedness: the input is quasi-compactness alone. The property is the
longhand lambda rather than `AlgebraicGeometry.Space.quasiCompactProperty`, so neither
Stacks 03HF nor Stacks 041L is needed even though both are available. -/
@[stacks 050I "part (5): quasi-compact"]
theorem isQuasiCompact_graph (g : 𝒳 ⟶ 𝒴) (p : 𝒳 ⟶ 𝒯) (q : 𝒴 ⟶ 𝒯) (η : p ≅ g ≫ q)
    (hq : AlgebraicStacks.IsQuasiSeparated B S hS q) :
    IsQuasiCompact B S hS (graph B S hS g p q η).hom :=
  relativeProperty_graph_of_comparison B S hS
    (fun _ _ k => Space.IsQuasiCompact B S hS k.hom) g p q η
    (isQuasiCompact_comparison B S hS g (𝟙 𝒴) q hq)

/-- **Stacks 050I, part (5), the quasi-separatedness half.** If `q : 𝒴 ⟶ 𝒯` is quasi-separated
then the graph of `g : 𝒳 ⟶ 𝒴` over `𝒯` is quasi-separated, in the sense of Properties of Stacks,
Section 04XB.

As for the quasi-compactness half, over the second conjunct: Stacks 050H part (7) is stated
twice, once for each conjunct of the quasi-separatedness condition of Stacks 04YW, so the input
here is quasi-separatedness of the comparison 1-morphism alone. -/
@[stacks 050I "part (5): quasi-separated"]
theorem isQuasiSeparated_graph (g : 𝒳 ⟶ 𝒴) (p : 𝒳 ⟶ 𝒯) (q : 𝒴 ⟶ 𝒯) (η : p ≅ g ≫ q)
    (hq : AlgebraicStacks.IsQuasiSeparated B S hS q) :
    IsQuasiSeparated B S hS (graph B S hS g p q η).hom :=
  relativeProperty_graph_of_comparison B S hS
    (fun _ _ k => Space.IsQuasiSeparated B S hS k.hom) g p q η
    (isQuasiSeparated_comparison B S hS g (𝟙 𝒴) q hq)

end AlgebraicGeometry.Stack

end
