module

public import StacksFrontier.CategoryTheory.FiberedInGroupoids.Fibrewise
public import StacksFrontier.CategoryTheory.FiberedInGroupoids.Representability.FibreFunctors
public import StacksFrontier.CategoryTheory.FiberedInGroupoids.Representability.SliceProduct
public import StacksFrontier.CategoryTheory.FiberedInGroupoids.TwoCategory
public import StacksFrontier.CategoryTheory.TwoFibreProductOverReindex
public import StacksFrontier.AlgebraicGeometry.Stacks.Algebraic.RepresentableMorphism.Product
import StacksCore.Tactic.StacksAttribute
import all StacksFrontier.AlgebraicGeometry.Stacks.Algebraic.RepresentableMorphism.Product

/-!
# Representability of a 1-morphism is invariant under equivalence

Let

```
𝒳' --f'--> 𝒴'
 |          |
 a          b
 |          |
 v          v
 𝒳 ---f---> 𝒴
```

be a 2-commutative square of categories fibred in groupoids over a base category in which the
vertical 1-morphisms `a` and `b` are equivalences. Then `f` is representable if and only if
`f'` is.

The proof is the one in the source: for a 1-morphism `G : 𝒞/U ⥤ 𝒴'` over the base, the two
2-fibre products `(𝒞/U) ×_{𝒴'} 𝒳'` and `(𝒞/U) ×_𝒴 𝒳` are compared by a chain of
equivalences — postcomposing the comparison isomorphism of the square, reindexing along it,
and precomposing with `a` — each of which is an equivalence over `𝒞/U`, and representability
of a category fibred in groupoids transfers along an equivalence over the base.

## Main results

* `Stacks.RepresentableMorphism.isRepresentableMorphism_iff_of_equivalences`: representability of a
  1-morphism is invariant under equivalences in a 2-commutative square.

## Implementation notes

The statement is made over an arbitrary base category, of which the big fppf site over a
scheme is a special case. The 2-commutativity of the square is expressed as an isomorphism of
1-morphisms in the 2-category of categories fibred in groupoids over the base; in particular
its components lie over identities of the base, which is what the reindexing step needs.

## References

* [Stacks Project, Tag 0456](https://stacks.math.columbia.edu/tag/0456)
-/

@[expose] public section

open CategoryTheory

namespace Stacks.RepresentableMorphism

universe v₁ v₂ u₁ u₂

variable {𝒞 : Type u₁} [Category.{v₁} 𝒞]
variable {𝒳' 𝒳 𝒴' 𝒴 : CatFiberedInGroupoids.{v₁, v₂, u₁, u₂} 𝒞}

universe vA vB vD uA uB uD

private theorem representableCFG_iff_of_equivalence
    {𝒜 : Type uA} {ℬ : Type uB} [Category.{vA} 𝒜] [Category.{vB} ℬ]
    (p : 𝒜 ⥤ 𝒞) (q : ℬ ⥤ 𝒞) (hp : p.IsFiberedInGroupoids)
    (hq : q.IsFiberedInGroupoids) (F : 𝒜 ⥤ ℬ) (hF : F ⋙ q = p)
    [Functor.IsEquivalence F] :
    Stacks.RepresentableMorphism.IsRepresentableCFG p ↔
      Stacks.RepresentableMorphism.IsRepresentableCFG q := by
  obtain ⟨H, hH, η, ε, hη, hε⟩ :=
    Functor.IsFiberedInGroupoids.isEquivalence_over p q hp hq F hF inferInstance
  have : Functor.IsEquivalence H :=
    (CategoryTheory.Equivalence.mk F H η.symm ε).symm.isEquivalence_functor
  exact ⟨representableCFG_of_equivalence p q hq H hH, representableCFG_of_equivalence q p hp F hF⟩

private def product_postcompose
    {𝒜 : Type uA} {ℬ : Type uB} {𝒟 : Type uD}
    [Category.{vA} 𝒜] [Category.{vB} ℬ] [Category.{vD} 𝒟]
    {p𝒜 : 𝒜 ⥤ 𝒞} {pℬ : ℬ ⥤ 𝒞} {p𝒟 : 𝒟 ⥤ 𝒞}
    {T : Type u₂} [Category.{v₂} T] {pT : T ⥤ 𝒞}
    (G : T ⥤ ℬ) (F : 𝒜 ⥤ ℬ) (b : ℬ ⥤ 𝒟)
    (hb : b ⋙ p𝒟 = pℬ) :
    TwoFibreProductOver pT p𝒜 pℬ G F ⥤
      TwoFibreProductOver pT p𝒜 p𝒟 (G ⋙ b) (F ⋙ b) where
  obj P :=
    { base := P.base
      x := P.x
      y := P.y
      hx := P.hx
      hy := P.hy
      iso := b.mapIso P.iso
      vertical := by
        have := P.vertical
        simpa using Functor.isHomLift_map_of_comp_eq hb (𝟙 P.base) P.iso.hom }
  map {P Q} f :=
    { hbase := f.hbase
      a := f.a
      b := f.b
      ha := f.ha
      hb := f.hb
      w := by
        simpa only [Functor.comp_map, Functor.mapIso_hom, Functor.map_comp] using
          congrArg b.map f.w }
  map_id P := by apply TwoFibreProductOver.Hom.ext <;> rfl
  map_comp f g := by apply TwoFibreProductOver.Hom.ext <;> rfl

private theorem product_postcompose_isEquivalence
    {𝒜 : Type uA} {ℬ : Type uB} {𝒟 : Type uD}
    [Category.{vA} 𝒜] [Category.{vB} ℬ] [Category.{vD} 𝒟]
    {p𝒜 : 𝒜 ⥤ 𝒞} {pℬ : ℬ ⥤ 𝒞} {p𝒟 : 𝒟 ⥤ 𝒞}
    {T : Type u₂} [Category.{v₂} T] {pT : T ⥤ 𝒞}
    {G : T ⥤ ℬ} {F : 𝒜 ⥤ ℬ} {b : ℬ ⥤ 𝒟}
    (hb : b ⋙ p𝒟 = pℬ) [Functor.IsEquivalence b] :
    (product_postcompose (p𝒜 := p𝒜) (pT := pT) G F b hb).IsEquivalence := by
  let K := product_postcompose (p𝒜 := p𝒜) (pT := pT) G F b hb
  have hfaith : K.Faithful := by
    constructor
    intro P Q f g h
    have ha : f.a = g.a := by
      simpa only [K, product_postcompose] using congrArg TwoFibreProductOver.Hom.a h
    have hb' : f.b = g.b := by
      simpa only [K, product_postcompose] using congrArg TwoFibreProductOver.Hom.b h
    exact TwoFibreProductOver.Hom.ext' ha hb'
  have hfull : K.Full := by
    constructor
    intro P Q f
    refine ⟨⟨f.hbase, f.a, f.b, f.ha, f.hb, ?_⟩, ?_⟩
    · apply b.map_injective
      simpa only [K, product_postcompose, Functor.comp_map, Functor.mapIso_hom,
        Functor.map_comp] using f.w
    · apply TwoFibreProductOver.Hom.ext' <;> rfl
  have hess : K.EssSurj := by
    constructor
    intro Q
    let i : G.obj Q.x ≅ F.obj Q.y := (Functor.FullyFaithful.ofFullyFaithful b).preimageIso Q.iso
    have hi : b.mapIso i = Q.iso :=
      Iso.ext ((Functor.FullyFaithful.ofFullyFaithful b).map_preimage Q.iso.hom)
    have hivert : pℬ.IsHomLift (𝟙 Q.base) i.hom := by
      have h : p𝒟.IsHomLift (𝟙 Q.base) (b.map i.hom) := by
        rw [show b.map i.hom = Q.iso.hom from congrArg Iso.hom hi]
        exact Q.vertical
      exact (Functor.isHomLift_map_iff_of_comp_eq pℬ p𝒟 b hb
        (𝟙 Q.base) i.hom).1 h
    let P : TwoFibreProductOver pT p𝒜 pℬ G F :=
      { base := Q.base, x := Q.x, y := Q.y, hx := Q.hx, hy := Q.hy,
        iso := i, vertical := hivert }
    have hobj : K.obj P = Q := by
      apply TwoFibreProductOver.obj_ext
      simpa [P, K, product_postcompose] using hi
    exact ⟨P, ⟨eqToIso hobj⟩⟩
  exact { faithful := hfaith, full := hfull, essSurj := hess }

private def product_swap
    {𝒜 : Type uA} {ℬ : Type uB} {𝒟 : Type uD}
    [Category.{vA} 𝒜] [Category.{vB} ℬ] [Category.{vD} 𝒟]
    {p𝒜 : 𝒜 ⥤ 𝒞} {pℬ : ℬ ⥤ 𝒞} {p𝒟 : 𝒟 ⥤ 𝒞}
    {F : 𝒜 ⥤ 𝒟} {G : ℬ ⥤ 𝒟} :
    TwoFibreProductOver p𝒜 pℬ p𝒟 F G ⥤ TwoFibreProductOver pℬ p𝒜 p𝒟 G F where
  obj P :=
    { base := P.base
      x := P.y
      y := P.x
      hx := P.hy
      hy := P.hx
      iso := P.iso.symm
      vertical := by
        let : p𝒟.IsHomLift (𝟙 P.base) P.iso.hom := P.vertical
        exact IsHomLift.lift_id_inv p𝒟 P.base P.iso }
  map {P Q} f :=
    { hbase := f.hbase
      a := f.b
      b := f.a
      ha := f.hb
      hb := f.ha
      w := by
        apply (cancel_mono Q.iso.hom).mp
        calc
          (G.map f.b ≫ Q.iso.inv) ≫ Q.iso.hom = G.map f.b := by simp [Category.assoc]
          _ = (P.iso.inv ≫ F.map f.a) ≫ Q.iso.hom := by
                calc
                  G.map f.b = P.iso.inv ≫ (P.iso.hom ≫ G.map f.b) := by simp
                  _ = P.iso.inv ≫ (F.map f.a ≫ Q.iso.hom) := by rw [f.w]
                  _ = (P.iso.inv ≫ F.map f.a) ≫ Q.iso.hom := by rw [Category.assoc] }
  map_id P := by apply TwoFibreProductOver.Hom.ext <;> rfl
  map_comp f g := by apply TwoFibreProductOver.Hom.ext <;> rfl

private theorem product_swap_essSurj
    {𝒜 : Type uA} {ℬ : Type uB} {𝒟 : Type uD}
    [Category.{vA} 𝒜] [Category.{vB} ℬ] [Category.{vD} 𝒟]
    {p𝒜 : 𝒜 ⥤ 𝒞} {pℬ : ℬ ⥤ 𝒞} {p𝒟 : 𝒟 ⥤ 𝒞}
    {F : 𝒜 ⥤ 𝒟} {G : ℬ ⥤ 𝒟} :
    (product_swap (p𝒜 := p𝒜) (pℬ := pℬ) (p𝒟 := p𝒟) (F := F) (G := G)).EssSurj := by
  constructor
  intro Q
  let P : TwoFibreProductOver p𝒜 pℬ p𝒟 F G :=
    { base := Q.base, x := Q.y, y := Q.x, hx := Q.hy, hy := Q.hx,
      iso := Q.iso.symm, vertical := by
        have : p𝒟.IsHomLift (𝟙 Q.base) Q.iso.hom := Q.vertical
        exact IsHomLift.lift_id_inv p𝒟 Q.base Q.iso }
  refine ⟨P, ⟨eqToIso ?_⟩⟩
  apply TwoFibreProductOver.obj_ext
  apply Iso.ext
  simp [P]

private theorem product_swap_isEquivalence
    {𝒜 : Type uA} {ℬ : Type uB} {𝒟 : Type uD}
    [Category.{vA} 𝒜] [Category.{vB} ℬ] [Category.{vD} 𝒟]
    {p𝒜 : 𝒜 ⥤ 𝒞} {pℬ : ℬ ⥤ 𝒞} {p𝒟 : 𝒟 ⥤ 𝒞}
    {F : 𝒜 ⥤ 𝒟} {G : ℬ ⥤ 𝒟} :
    (product_swap (p𝒜 := p𝒜) (pℬ := pℬ) (p𝒟 := p𝒟) (F := F) (G := G)).IsEquivalence := by
  let K := product_swap (p𝒜 := p𝒜) (pℬ := pℬ) (p𝒟 := p𝒟) (F := F) (G := G)
  have hfaith : K.Faithful := by
    constructor
    intro P Q f g h
    have ha : f.b = g.b := by
      simpa only [K, product_swap] using congrArg TwoFibreProductOver.Hom.a h
    have hb : f.a = g.a := by
      simpa only [K, product_swap] using congrArg TwoFibreProductOver.Hom.b h
    exact TwoFibreProductOver.Hom.ext' hb ha
  have hfull : K.Full := by
    constructor
    intro P Q f
    let a₀ : P.x ⟶ Q.x := by simpa [K, product_swap] using f.b
    let b₀ : P.y ⟶ Q.y := by simpa [K, product_swap] using f.a
    have hPx : (K.obj P).y = P.x := rfl
    have hQx : (K.obj Q).y = Q.x := rfl
    have hPy : (K.obj P).x = P.y := rfl
    have hQy : (K.obj Q).x = Q.y := rfl
    have ha₀ : a₀ = f.b := by
      dsimp [a₀]
      cases hPx
      cases hQx
      rfl
    have hb₀ : b₀ = f.a := by
      dsimp [b₀]
      cases hPy
      cases hQy
      rfl
    have hfa : p𝒜.IsHomLift f.hbase a₀ := by simpa [ha₀, K, product_swap] using f.hb
    have hfb : pℬ.IsHomLift f.hbase b₀ := by simpa [hb₀, K, product_swap] using f.ha
    refine ⟨⟨f.hbase, a₀, b₀, hfa, hfb, ?_⟩, ?_⟩
    · have htarget : G.map b₀ ≫ Q.iso.inv = P.iso.inv ≫ F.map a₀ := by
        simpa [K, product_swap, ha₀, hb₀, Iso.symm_hom] using f.w
      calc
        F.map a₀ ≫ Q.iso.hom =
            P.iso.hom ≫ ((P.iso.inv ≫ F.map a₀) ≫ Q.iso.hom) := by simp [Category.assoc]
        _ = P.iso.hom ≫ ((G.map b₀ ≫ Q.iso.inv) ≫ Q.iso.hom) := by rw [← htarget]
        _ = P.iso.hom ≫ G.map b₀ := by simp [Category.assoc]
    · exact TwoFibreProductOver.Hom.ext' hb₀ ha₀
  exact { faithful := hfaith, full := hfull, essSurj := product_swap_essSurj }

private def product_precompose_source
    {𝒜' : Type uA} {𝒜 : Type uB} {ℬ : Type uD}
    [Category.{vA} 𝒜'] [Category.{vB} 𝒜] [Category.{vD} ℬ]
    {p𝒜' : 𝒜' ⥤ 𝒞} {p𝒜 : 𝒜 ⥤ 𝒞} {pℬ : ℬ ⥤ 𝒞}
    {T : Type u₂} [Category.{v₂} T] {pT : T ⥤ 𝒞}
    (G : T ⥤ ℬ) (F : 𝒜 ⥤ ℬ) (a : 𝒜' ⥤ 𝒜)
    (hA : a ⋙ p𝒜 = p𝒜') :
    TwoFibreProductOver pT p𝒜' pℬ G (a ⋙ F) ⥤
      TwoFibreProductOver pT p𝒜 pℬ G F where
  obj P :=
    { base := P.base
      x := P.x
      y := a.obj P.y
      hx := P.hx
      hy := (Functor.congr_obj hA P.y).trans P.hy
      iso := P.iso
      vertical := P.vertical }
  map {P Q} f :=
    { hbase := f.hbase
      a := f.a
      b := a.map f.b
      ha := f.ha
      hb := by
        have : p𝒜'.IsHomLift f.hbase f.b := f.hb
        exact Functor.isHomLift_map_of_comp_eq
          (p := p𝒜') (q := p𝒜) (G := a) hA f.hbase f.b
      w := by simpa only [Functor.comp_map] using f.w }
  map_id P := by apply TwoFibreProductOver.Hom.ext <;> simp
  map_comp f g := by apply TwoFibreProductOver.Hom.ext <;> simp

private theorem product_precompose_source_essSurj
    {𝒜' : Type uA} {𝒜 : Type uB} {ℬ : Type uD}
    [Category.{vA} 𝒜'] [Category.{vB} 𝒜] [Category.{vD} ℬ]
    {p𝒜' : 𝒜' ⥤ 𝒞} {p𝒜 : 𝒜 ⥤ 𝒞} {pℬ : ℬ ⥤ 𝒞}
    {T : Type u₂} [Category.{v₂} T] {pT : T ⥤ 𝒞}
    {G : T ⥤ ℬ} {F : 𝒜 ⥤ ℬ} {a : 𝒜' ⥤ 𝒜}
    (hpT : pT.IsFiberedInGroupoids)
    (hp𝒜' : p𝒜'.IsFiberedInGroupoids) (hp𝒜 : p𝒜.IsFiberedInGroupoids)
    (hA : a ⋙ p𝒜 = p𝒜') [Functor.IsEquivalence a] (hF : F ⋙ pℬ = p𝒜) :
    (product_precompose_source (p𝒜' := p𝒜') (p𝒜 := p𝒜) (pℬ := pℬ)
      (pT := pT) G F a hA).EssSurj := by
  let K := product_precompose_source (p𝒜' := p𝒜') (p𝒜 := p𝒜) (pℬ := pℬ)
    (pT := pT) G F a hA
  constructor
  intro P
  obtain ⟨x', hx', e, he⟩ :=
    Functor.quasiInverse_choice p𝒜' p𝒜 hp𝒜' hp𝒜 a hA inferInstance P.y
  have heInv : p𝒜.IsHomLift (𝟙 (p𝒜.obj P.y)) e.inv :=
    IsHomLift.lift_id_inv p𝒜 (p𝒜.obj P.y) e
  have hvFe : pℬ.IsHomLift (𝟙 P.base) (F.map e.hom) := by
    rw [← P.hy]
    exact Functor.isHomLift_map_of_comp_eq hF (𝟙 (p𝒜.obj P.y)) e.hom
  have hvIso : pℬ.IsHomLift (𝟙 P.base)
      ((P.iso ≪≫ F.mapIso e).hom) := by
    have : pℬ.IsHomLift (𝟙 P.base) P.iso.hom := P.vertical
    dsimp only [Iso.trans_hom, Functor.mapIso_hom]
    infer_instance
  let Q : TwoFibreProductOver pT p𝒜' pℬ G (a ⋙ F) :=
    { base := P.base, x := P.x, y := x', hx := P.hx,
      hy := hx'.trans P.hy,
      iso := P.iso ≪≫ F.mapIso e, vertical := hvIso }
  let Φ : K.obj Q ⟶ P := by
    dsimp [K, product_precompose_source, Q]
    exact TwoFibreProductOver.Hom.mk' (𝟙 P.x) e.inv (by
        rw [IsHomLift.fac' p𝒜 (𝟙 (p𝒜.obj P.y)) e.inv]
        simp [eqToHom_trans]) (by
          simp [Category.assoc])
  have hΦ : (TwoFibreProductOver.structureFunctor pT p𝒜 pℬ G F).IsHomLift
      (𝟙 P.base) Φ := by
    have hmap : (TwoFibreProductOver.structureFunctor pT p𝒜 pℬ G F).map Φ =
        𝟙 P.base := by
      change eqToHom P.hx.symm ≫ pT.map (𝟙 P.x) ≫ eqToHom P.hx = 𝟙 P.base
      rw [pT.map_id, Category.id_comp, eqToHom_trans, eqToHom_refl]
    rw [← hmap]
    exact IsHomLift.map (TwoFibreProductOver.structureFunctor pT p𝒜 pℬ G F) Φ
  have : IsIso Φ :=
    TwoFibreProductOver.isIso_of_isHomLift_id hpT hp𝒜 Φ hΦ
  exact ⟨Q, ⟨asIso Φ⟩⟩

private theorem product_precompose_source_isEquivalence
    {𝒜' : Type uA} {𝒜 : Type uB} {ℬ : Type uD}
    [Category.{vA} 𝒜'] [Category.{vB} 𝒜] [Category.{vD} ℬ]
    {p𝒜' : 𝒜' ⥤ 𝒞} {p𝒜 : 𝒜 ⥤ 𝒞} {pℬ : ℬ ⥤ 𝒞}
    {T : Type u₂} [Category.{v₂} T] {pT : T ⥤ 𝒞}
    {G : T ⥤ ℬ} {F : 𝒜 ⥤ ℬ} {a : 𝒜' ⥤ 𝒜}
    (hpT : pT.IsFiberedInGroupoids)
    (hp𝒜' : p𝒜'.IsFiberedInGroupoids) (hp𝒜 : p𝒜.IsFiberedInGroupoids)
    (hA : a ⋙ p𝒜 = p𝒜') [Functor.IsEquivalence a]
    (_hG : G ⋙ pℬ = pT) (hF : F ⋙ pℬ = p𝒜) :
    (product_precompose_source (p𝒜' := p𝒜') (p𝒜 := p𝒜) (pℬ := pℬ)
      (pT := pT) G F a hA).IsEquivalence := by
  let K := product_precompose_source (p𝒜' := p𝒜') (p𝒜 := p𝒜) (pℬ := pℬ)
    (pT := pT) G F a hA
  have hfaith : K.Faithful := by
    constructor
    intro P Q f g h
    have ha : f.a = g.a := by
      simpa only [K, product_precompose_source] using
        congrArg TwoFibreProductOver.Hom.a h
    have hb : a.map f.b = a.map g.b := by
      simpa only [K, product_precompose_source] using
        congrArg TwoFibreProductOver.Hom.b h
    exact TwoFibreProductOver.Hom.ext' ha (a.map_injective hb)
  have hfull : K.Full := by
    constructor
    intro P Q f
    obtain ⟨v, hv⟩ := a.map_surjective f.b
    have hfb : p𝒜.IsHomLift f.hbase (a.map v) := by
      simpa [K, product_precompose_source, hv] using f.hb
    have hvlift : p𝒜'.IsHomLift f.hbase v :=
      (Functor.isHomLift_map_iff_of_comp_eq p𝒜' p𝒜 a hA f.hbase v).1 hfb
    refine ⟨⟨f.hbase, f.a, v, f.ha, hvlift, ?_⟩, ?_⟩
    · simpa [K, product_precompose_source, Functor.comp_map, hv] using f.w
    · exact TwoFibreProductOver.Hom.ext' rfl hv
  exact { faithful := hfaith, full := hfull,
          essSurj := product_precompose_source_essSurj hpT hp𝒜' hp𝒜 hA hF }

private def product_reindex_second
    {𝒜 : Type uA} {𝒟 : Type uD}
    [Category.{vA} 𝒜] [Category.{vD} 𝒟]
    {p𝒜 : 𝒜 ⥤ 𝒞} {p𝒟 : 𝒟 ⥤ 𝒞}
    {T : Type u₂} [Category.{v₂} T] {pT : T ⥤ 𝒞}
    {F : T ⥤ 𝒟} {G G' : 𝒜 ⥤ 𝒟}
    (α : G ≅ G') (hα : ∀ x, p𝒟.IsHomLift (𝟙 (p𝒜.obj x)) (α.hom.app x)) :
    TwoFibreProductOver pT p𝒜 p𝒟 F G ⥤ TwoFibreProductOver pT p𝒜 p𝒟 F G' where
  obj P :=
    { base := P.base
      x := P.x
      y := P.y
      hx := P.hx
      hy := P.hy
      iso := P.iso ≪≫ α.app P.y
      vertical := by
        have hα' : p𝒟.IsHomLift (𝟙 P.base) (α.hom.app P.y) := by
          rw [← P.hy]
          exact hα P.y
        let : p𝒟.IsHomLift (𝟙 P.base) P.iso.hom := P.vertical
        let : p𝒟.IsHomLift (𝟙 P.base) (α.app P.y).hom := hα'
        dsimp only [Iso.trans_hom]
        exact IsHomLift.comp_of_lift_id p𝒟 P.base P.iso.hom (α.app P.y).hom }
  map {P Q} f :=
    { hbase := f.hbase
      a := f.a
      b := f.b
      ha := f.ha
      hb := f.hb
      w := by
        dsimp only [Iso.trans_hom]
        calc
          F.map f.a ≫ Q.iso.hom ≫ α.hom.app Q.y =
              (F.map f.a ≫ Q.iso.hom) ≫ α.hom.app Q.y := by simp [Category.assoc]
          _ = (P.iso.hom ≫ G.map f.b) ≫ α.hom.app Q.y := by rw [f.w]
          _ = P.iso.hom ≫ (G.map f.b ≫ α.hom.app Q.y) := by rw [Category.assoc]
          _ = P.iso.hom ≫ (α.hom.app P.y ≫ G'.map f.b) := by
                rw [α.hom.naturality f.b]
          _ = (P.iso.hom ≫ α.hom.app P.y) ≫ G'.map f.b := by rw [Category.assoc] }
  map_id P := by apply TwoFibreProductOver.Hom.ext <;> rfl
  map_comp f g := by apply TwoFibreProductOver.Hom.ext <;> rfl

private theorem product_reindex_second_isEquivalence
    {𝒜 : Type uA} {𝒟 : Type uD}
    [Category.{vA} 𝒜] [Category.{vD} 𝒟]
    {p𝒜 : 𝒜 ⥤ 𝒞} {p𝒟 : 𝒟 ⥤ 𝒞}
    {T : Type u₂} [Category.{v₂} T] {pT : T ⥤ 𝒞}
    {F : T ⥤ 𝒟} {G G' : 𝒜 ⥤ 𝒟}
    (α : G ≅ G') (hα : ∀ x, p𝒟.IsHomLift (𝟙 (p𝒜.obj x)) (α.hom.app x)) :
    (product_reindex_second (F := F) (p𝒜 := p𝒜) (p𝒟 := p𝒟)
      (pT := pT) α hα).IsEquivalence := by
  let K := product_reindex_second (F := F) (p𝒜 := p𝒜) (p𝒟 := p𝒟)
    (pT := pT) α hα
  have hfaith : K.Faithful := by
    constructor
    intro P Q f g h
    have ha : f.a = g.a := by
      simpa only [K, product_reindex_second] using congrArg TwoFibreProductOver.Hom.a h
    have hb : f.b = g.b := by
      simpa only [K, product_reindex_second] using congrArg TwoFibreProductOver.Hom.b h
    exact TwoFibreProductOver.Hom.ext' ha hb
  have hfull : K.Full := by
    constructor
    intro P Q f
    refine ⟨⟨f.hbase, f.a, f.b, f.ha, f.hb, ?_⟩, ?_⟩
    · have hαP : G.map f.b ≫ (α.app Q.y).hom = (α.app P.y).hom ≫ G'.map f.b :=
        α.hom.naturality f.b
      have hcancel : (F.map f.a ≫ Q.iso.hom) ≫ (α.app Q.y).hom =
          (P.iso.hom ≫ G.map f.b) ≫ (α.app Q.y).hom := by
        simpa [K, product_reindex_second, Category.assoc, ← hαP] using f.w
      exact (cancel_mono (α.app Q.y).hom).mp hcancel
    · apply TwoFibreProductOver.Hom.ext' <;> rfl
  have hess : K.EssSurj := by
    constructor
    intro Q
    have hαinv : p𝒟.IsHomLift (𝟙 Q.base) (α.app Q.y).inv := by
      have hi : p𝒟.IsHomLift (𝟙 (p𝒜.obj Q.y)) (α.app Q.y).inv := by
        let : p𝒟.IsHomLift (𝟙 (p𝒜.obj Q.y)) (α.app Q.y).hom := hα Q.y
        exact IsHomLift.lift_id_inv p𝒟 (p𝒜.obj Q.y) (α.app Q.y)
      rw [← Q.hy]
      exact hi
    let P : TwoFibreProductOver pT p𝒜 p𝒟 F G :=
      { base := Q.base, x := Q.x, y := Q.y, hx := Q.hx, hy := Q.hy,
        iso := Q.iso ≪≫ (α.app Q.y).symm, vertical := by
          let : p𝒟.IsHomLift (𝟙 Q.base) Q.iso.hom := Q.vertical
          let : p𝒟.IsHomLift (𝟙 Q.base) (α.app Q.y).inv := hαinv
          dsimp only [Iso.trans_hom, Iso.symm_hom]
          infer_instance }
    have hobj : K.obj P = Q := by
      apply TwoFibreProductOver.obj_ext
      apply Iso.ext
      simp [P]
    exact ⟨P, ⟨eqToIso hobj⟩⟩
  exact { faithful := hfaith, full := hfull, essSurj := hess }

private def product_reindex_first
    {𝒜 : Type uA} {ℬ : Type uB} {𝒟 : Type uD}
    [Category.{vA} 𝒜] [Category.{vB} ℬ] [Category.{vD} 𝒟]
    {p𝒜 : 𝒜 ⥤ 𝒞} {pℬ : ℬ ⥤ 𝒞} {p𝒟 : 𝒟 ⥤ 𝒞}
    {F F' : 𝒜 ⥤ 𝒟} {G : ℬ ⥤ 𝒟}
    (α : F ≅ F') (hα : ∀ x, p𝒟.IsHomLift (𝟙 (p𝒜.obj x)) (α.hom.app x)) :
    TwoFibreProductOver p𝒜 pℬ p𝒟 F G ⥤ TwoFibreProductOver p𝒜 pℬ p𝒟 F' G :=
  product_swap (p𝒜 := p𝒜) (pℬ := pℬ) (p𝒟 := p𝒟) (F := F) (G := G) ⋙
    product_reindex_second (F := G) (G := F) (G' := F') (p𝒜 := p𝒜) (p𝒟 := p𝒟)
      (pT := pℬ) α hα ⋙
    product_swap (p𝒜 := pℬ) (pℬ := p𝒜) (p𝒟 := p𝒟) (F := G) (G := F')

private theorem product_reindex_first_isEquivalence
    {𝒜 : Type uA} {ℬ : Type uB} {𝒟 : Type uD}
    [Category.{vA} 𝒜] [Category.{vB} ℬ] [Category.{vD} 𝒟]
    {p𝒜 : 𝒜 ⥤ 𝒞} {pℬ : ℬ ⥤ 𝒞} {p𝒟 : 𝒟 ⥤ 𝒞}
    {F F' : 𝒜 ⥤ 𝒟} {G : ℬ ⥤ 𝒟}
    (α : F ≅ F') (hα : ∀ x, p𝒟.IsHomLift (𝟙 (p𝒜.obj x)) (α.hom.app x)) :
    (product_reindex_first (p𝒜 := p𝒜) (pℬ := pℬ) (p𝒟 := p𝒟)
      (F := F) (F' := F') (G := G) α hα).IsEquivalence := by
  let S := product_swap (p𝒜 := p𝒜) (pℬ := pℬ) (p𝒟 := p𝒟) (F := F) (G := G)
  let R := product_reindex_second (F := G) (G := F) (G' := F')
    (p𝒜 := p𝒜) (p𝒟 := p𝒟) (pT := pℬ) α hα
  let T := product_swap (p𝒜 := pℬ) (pℬ := p𝒜) (p𝒟 := p𝒟) (F := G) (G := F')
  have : S.IsEquivalence := product_swap_isEquivalence
  have : R.IsEquivalence := product_reindex_second_isEquivalence
    (F := G) (p𝒜 := p𝒜) (p𝒟 := p𝒟) (pT := pℬ) α hα
  have : T.IsEquivalence := product_swap_isEquivalence
  have : (S ⋙ R).IsEquivalence := Functor.isEquivalence_trans S R
  change (S ⋙ R ⋙ T).IsEquivalence
  exact Functor.isEquivalence_trans (S ⋙ R) T

private def homFunctorIso {f' : 𝒳' ⟶ 𝒴'} {f : 𝒳 ⟶ 𝒴} {a : 𝒳' ⟶ 𝒳} {b : 𝒴' ⟶ 𝒴}
    (α : a ≫ f ≅ f' ≫ b) :
    CatFiberedInGroupoids.homFunctor a ⋙ CatFiberedInGroupoids.homFunctor f ≅
      CatFiberedInGroupoids.homFunctor f' ⋙ CatFiberedInGroupoids.homFunctor b := by
  refine NatIso.ofComponents (fun x => ?_) ?_
  · refine ⟨α.hom.hom.toNatTrans.app x, α.inv.hom.toNatTrans.app x, ?_, ?_⟩
    · have hcomp : α.hom.hom ≫ α.inv.hom = BasedNatTrans.id (a ≫ f).hom :=
        congrArg (fun t => t.hom) α.hom_inv_id
      have happ := congrArg
        (fun t : BasedNatTrans (a ≫ f).hom (a ≫ f).hom => t.toNatTrans.app x) hcomp
      change (α.hom.hom.comp α.inv.hom).toNatTrans.app x =
        (BasedNatTrans.id (a ≫ f).hom).toNatTrans.app x at happ
      rw [BasedNatTrans.comp_toNatTrans, NatTrans.vcomp_app,
        BasedNatTrans.id_toNatTrans] at happ
      convert happ using 1 <;> rfl
    · have hcomp : α.inv.hom ≫ α.hom.hom = BasedNatTrans.id (f' ≫ b).hom :=
        congrArg (fun t => t.hom) α.inv_hom_id
      have happ := congrArg
        (fun t : BasedNatTrans (f' ≫ b).hom (f' ≫ b).hom => t.toNatTrans.app x) hcomp
      change (α.inv.hom.comp α.hom.hom).toNatTrans.app x =
        (BasedNatTrans.id (f' ≫ b).hom).toNatTrans.app x at happ
      rw [BasedNatTrans.comp_toNatTrans, NatTrans.vcomp_app,
        BasedNatTrans.id_toNatTrans] at happ
      convert happ using 1 <;> rfl
  · intro x y g
    exact α.hom.hom.toNatTrans.naturality g

private theorem isHomLift_homFunctorIso_symm_app {f' : 𝒳' ⟶ 𝒴'} {f : 𝒳 ⟶ 𝒴}
    {a : 𝒳' ⟶ 𝒳} {b : 𝒴' ⟶ 𝒴} (α : a ≫ f ≅ f' ≫ b) (x : 𝒳'.val.obj) :
    𝒴.val.p.IsHomLift (𝟙 (𝒳'.val.p.obj x)) ((homFunctorIso α).symm.hom.app x) := by
  have hα (x : 𝒳'.val.obj) : 𝒴.val.p.IsHomLift
      (𝟙 (𝒳'.val.p.obj x)) ((homFunctorIso α).hom.app x) :=
    CatFiberedInGroupoids.isHomLift_app α.hom x
  exact TwoFibreProductOver.isHomLift_inv_app (homFunctorIso α) hα x

private theorem representableCFG_fst_iff (f' : 𝒳' ⟶ 𝒴') (f : 𝒳 ⟶ 𝒴) {U : 𝒞}
    {G' : Over U ⥤ 𝒴'.val.obj} {G : Over U ⥤ 𝒴.val.obj}
    (hG' : G' ⋙ 𝒴'.val.p = Over.forget U) (hG : G ⋙ 𝒴.val.p = Over.forget U)
    (K : TwoFibreProductOver (Over.forget U) 𝒳'.val.p 𝒴'.val.p G'
        (CatFiberedInGroupoids.homFunctor f') ⥤
      TwoFibreProductOver (Over.forget U) 𝒳.val.p 𝒴.val.p G
        (CatFiberedInGroupoids.homFunctor f))
    [K.IsEquivalence]
    (hK : K ⋙ TwoFibreProductOver.fst (Over.forget U) 𝒳.val.p 𝒴.val.p G
        (CatFiberedInGroupoids.homFunctor f) =
      TwoFibreProductOver.fst (Over.forget U) 𝒳'.val.p 𝒴'.val.p G'
        (CatFiberedInGroupoids.homFunctor f')) :
    IsRepresentableCFG (TwoFibreProductOver.fst (Over.forget U) 𝒳'.val.p 𝒴'.val.p G'
        (CatFiberedInGroupoids.homFunctor f')) ↔
      IsRepresentableCFG (TwoFibreProductOver.fst (Over.forget U) 𝒳.val.p 𝒴.val.p G
        (CatFiberedInGroupoids.homFunctor f)) :=
  representableCFG_iff_of_equivalence _ _
    (TwoFibreProductOver.fst_isFiberedInGroupoids U 𝒳'.val.p 𝒴'.val.p _ G'
      𝒳'.isFiberedInGroupoids 𝒴'.isFiberedInGroupoids
      (CatFiberedInGroupoids.homFunctor_comp_p f') hG')
    (TwoFibreProductOver.fst_isFiberedInGroupoids U 𝒳.val.p 𝒴.val.p _ G
      𝒳.isFiberedInGroupoids 𝒴.isFiberedInGroupoids
      (CatFiberedInGroupoids.homFunctor_comp_p f) hG)
    K hK

private theorem representableCFG_fst_iff_of_iso
    (f' : 𝒳' ⟶ 𝒴') (f : 𝒳 ⟶ 𝒴) (a : 𝒳' ⟶ 𝒳) (b : 𝒴' ⟶ 𝒴) (α : a ≫ f ≅ f' ≫ b)
    [Functor.IsEquivalence (CatFiberedInGroupoids.homFunctor a)]
    [Functor.IsEquivalence (CatFiberedInGroupoids.homFunctor b)]
    {U : 𝒞} {G' : Over U ⥤ 𝒴'.val.obj} {G : Over U ⥤ 𝒴.val.obj}
    (hG' : G' ⋙ 𝒴'.val.p = Over.forget U) (hG : G ⋙ 𝒴.val.p = Over.forget U)
    (θ : G' ⋙ CatFiberedInGroupoids.homFunctor b ≅ G)
    (hθ : ∀ z, 𝒴.val.p.IsHomLift (𝟙 ((Over.forget U).obj z)) (θ.hom.app z)) :
    IsRepresentableCFG (TwoFibreProductOver.fst (Over.forget U) 𝒳'.val.p 𝒴'.val.p G'
        (CatFiberedInGroupoids.homFunctor f')) ↔
      IsRepresentableCFG (TwoFibreProductOver.fst (Over.forget U) 𝒳.val.p 𝒴.val.p G
        (CatFiberedInGroupoids.homFunctor f)) := by
  let a₀ := CatFiberedInGroupoids.homFunctor a
  let b₀ := CatFiberedInGroupoids.homFunctor b
  let f₀ := CatFiberedInGroupoids.homFunctor f
  let f'₀ := CatFiberedInGroupoids.homFunctor f'
  have ha : a₀ ⋙ 𝒳.val.p = 𝒳'.val.p := CatFiberedInGroupoids.homFunctor_comp_p a
  have hb : b₀ ⋙ 𝒴.val.p = 𝒴'.val.p := CatFiberedInGroupoids.homFunctor_comp_p b
  have hf : f₀ ⋙ 𝒴.val.p = 𝒳.val.p := CatFiberedInGroupoids.homFunctor_comp_p f
  let K₁ := product_postcompose (p𝒜 := 𝒳'.val.p) (pℬ := 𝒴'.val.p)
    (p𝒟 := 𝒴.val.p) (pT := Over.forget U) G' f'₀ b₀ hb
  let K₂ := product_reindex_first (p𝒜 := Over.forget U) (pℬ := 𝒳'.val.p)
    (p𝒟 := 𝒴.val.p) (F := G' ⋙ b₀) (F' := G) (G := f'₀ ⋙ b₀) θ hθ
  let K₃ := product_reindex_second (p𝒜 := 𝒳'.val.p) (p𝒟 := 𝒴.val.p)
    (pT := Over.forget U) (F := G) (G := f'₀ ⋙ b₀) (G' := a₀ ⋙ f₀)
    (homFunctorIso α).symm (isHomLift_homFunctorIso_symm_app α)
  let K₄ := product_precompose_source (p𝒜' := 𝒳'.val.p) (p𝒜 := 𝒳.val.p)
    (pℬ := 𝒴.val.p) (pT := Over.forget U) G f₀ a₀ ha
  let K := K₁ ⋙ K₂ ⋙ K₃ ⋙ K₄
  have : K₁.IsEquivalence := product_postcompose_isEquivalence hb
  have : K₂.IsEquivalence := product_reindex_first_isEquivalence
    (p𝒜 := Over.forget U) (pℬ := 𝒳'.val.p) (p𝒟 := 𝒴.val.p)
    (F := G' ⋙ b₀) (F' := G) (G := f'₀ ⋙ b₀) θ hθ
  have : K₃.IsEquivalence := product_reindex_second_isEquivalence
    (p𝒜 := 𝒳'.val.p) (p𝒟 := 𝒴.val.p) (pT := Over.forget U) (F := G) (G := f'₀ ⋙ b₀)
    (G' := a₀ ⋙ f₀) (homFunctorIso α).symm (isHomLift_homFunctorIso_symm_app α)
  have : K₄.IsEquivalence := product_precompose_source_isEquivalence
    (pT := Over.forget U) (p𝒜' := 𝒳'.val.p) (p𝒜 := 𝒳.val.p)
    (pℬ := 𝒴.val.p) (G := G) (F := f₀)
    (Functor.IsFiberedInGroupoids.over_forget U) 𝒳'.isFiberedInGroupoids
    𝒳.isFiberedInGroupoids ha hG hf
  have : K.IsEquivalence := inferInstanceAs (K₁ ⋙ K₂ ⋙ K₃ ⋙ K₄).IsEquivalence
  let FstNew := TwoFibreProductOver.fst (Over.forget U) 𝒳'.val.p 𝒴'.val.p G' f'₀
  let FstOld := TwoFibreProductOver.fst (Over.forget U) 𝒳.val.p 𝒴.val.p G f₀
  have hfst : K ⋙ FstOld = FstNew :=
    CategoryTheory.Functor.ext (fun P => rfl) (fun P Q g => by
      simp only [Functor.comp_map, K, K₁, K₂, K₃, K₄, FstOld, FstNew,
        product_postcompose, product_reindex_first, product_reindex_second,
        product_precompose_source, TwoFibreProductOver.fst_map]
      apply Over.OverMorphism.ext
      simp only [Over.comp_left]
      exact (conj_eqToHom_iff_heq' (Over.Hom.left g.a) (Over.Hom.left g.a)
        rfl rfl).2 HEq.rfl)
  exact representableCFG_fst_iff f' f hG' hG K hfst

/-- In a 2-commutative square whose vertical 1-morphisms are equivalences, the top
1-morphism is representable if the bottom one is. -/
private theorem isRepresentableMorphism_top_of_bottom
    (f' : 𝒳' ⟶ 𝒴') (f : 𝒳 ⟶ 𝒴) (a : 𝒳' ⟶ 𝒳) (b : 𝒴' ⟶ 𝒴) (α : a ≫ f ≅ f' ≫ b)
    [Functor.IsEquivalence (CatFiberedInGroupoids.homFunctor a)]
    [Functor.IsEquivalence (CatFiberedInGroupoids.homFunctor b)]
    (hrepr : IsRepresentableMorphism 𝒳.val.p 𝒴.val.p (CatFiberedInGroupoids.homFunctor f)) :
    IsRepresentableMorphism 𝒳'.val.p 𝒴'.val.p (CatFiberedInGroupoids.homFunctor f') := by
  intro U G' hG'
  have hG : (G' ⋙ CatFiberedInGroupoids.homFunctor b) ⋙ 𝒴.val.p = Over.forget U := by
    rw [Functor.assoc, CatFiberedInGroupoids.homFunctor_comp_p b, hG']
  refine (representableCFG_fst_iff_of_iso f' f a b α hG' hG (Iso.refl _) fun z => ?_).2
    (hrepr U _ hG)
  rw [← Functor.congr_obj hG z]
  change 𝒴.val.p.IsHomLift (𝟙 (𝒴.val.p.obj ((G' ⋙ CatFiberedInGroupoids.homFunctor b).obj z)))
    (𝟙 ((G' ⋙ CatFiberedInGroupoids.homFunctor b).obj z))
  infer_instance

/-- In a 2-commutative square whose vertical 1-morphisms are equivalences, the bottom
1-morphism is representable if the top one is. -/
private theorem isRepresentableMorphism_bottom_of_top
    (f' : 𝒳' ⟶ 𝒴') (f : 𝒳 ⟶ 𝒴) (a : 𝒳' ⟶ 𝒳) (b : 𝒴' ⟶ 𝒴) (α : a ≫ f ≅ f' ≫ b)
    [Functor.IsEquivalence (CatFiberedInGroupoids.homFunctor a)]
    [Functor.IsEquivalence (CatFiberedInGroupoids.homFunctor b)]
    (hrepr : IsRepresentableMorphism 𝒳'.val.p 𝒴'.val.p (CatFiberedInGroupoids.homFunctor f')) :
    IsRepresentableMorphism 𝒳.val.p 𝒴.val.p (CatFiberedInGroupoids.homFunctor f) := by
  intro U G hG
  let b₀ := CatFiberedInGroupoids.homFunctor b
  obtain ⟨H, hH, η, ε, hη, hε⟩ :=
    Functor.IsFiberedInGroupoids.isEquivalence_over 𝒴'.val.p 𝒴.val.p
      𝒴'.isFiberedInGroupoids 𝒴.isFiberedInGroupoids b₀
      (CatFiberedInGroupoids.homFunctor_comp_p b) inferInstance
  have hG' : (G ⋙ H) ⋙ 𝒴'.val.p = Over.forget U := by
    rw [Functor.assoc, hH, hG]
  let θ : (G ⋙ H) ⋙ b₀ ≅ G :=
    NatIso.ofComponents (fun z => ε.app (G.obj z)) (by
      intro z z' k
      convert ε.hom.naturality (G.map k) using 1 <;> simp [Functor.comp_map])
  have hθ (z : Over U) : 𝒴.val.p.IsHomLift (𝟙 ((Over.forget U).obj z)) (θ.hom.app z) := by
    rw [← Functor.congr_obj hG z]
    exact hε (G.obj z)
  exact (representableCFG_fst_iff_of_iso f' f a b α hG' hG θ hθ).1 (hrepr U _ hG')

/-- **Stacks 0456.** Representability of a 1-morphism of categories fibred in
groupoids is invariant under equivalences in a 2-commutative square. -/
@[stacks 0456]
public theorem isRepresentableMorphism_iff_of_equivalences
    (f' : 𝒳' ⟶ 𝒴') (f : 𝒳 ⟶ 𝒴)
    (a : 𝒳' ⟶ 𝒳) (b : 𝒴' ⟶ 𝒴)
    (α : a ≫ f ≅ f' ≫ b)
    [Functor.IsEquivalence (CatFiberedInGroupoids.homFunctor a)]
    [Functor.IsEquivalence (CatFiberedInGroupoids.homFunctor b)] :
    Stacks.RepresentableMorphism.IsRepresentableMorphism 𝒳.val.p 𝒴.val.p
      (CatFiberedInGroupoids.homFunctor f) ↔
    Stacks.RepresentableMorphism.IsRepresentableMorphism 𝒳'.val.p 𝒴'.val.p
      (CatFiberedInGroupoids.homFunctor f') :=
  ⟨isRepresentableMorphism_top_of_bottom f' f a b α,
    isRepresentableMorphism_bottom_of_top f' f a b α⟩


end Stacks.RepresentableMorphism
