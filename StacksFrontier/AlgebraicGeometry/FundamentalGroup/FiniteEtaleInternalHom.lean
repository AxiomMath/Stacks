module

public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.LocalFlatDescent
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.AlgebraicGeometry.QuasiAffine
public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import Mathlib.CategoryTheory.Comma.Over.Pullback
public import Mathlib.CategoryTheory.Limits.Constructions.Over.Products
public import StacksFrontier.AlgebraicGeometry.AmpleCluster.QuasiAffineAndImmersion
public import StacksFrontier.AlgebraicGeometry.Descent.FpqcAffine
public import StacksFrontier.AlgebraicGeometry.Descent.FpqcLocalAtTarget
public import StacksFrontier.AlgebraicGeometry.Etale.FiniteEtaleLocal
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFree.FiniteFlat
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFree.FpqcLocalAtTarget
public import StacksFrontier.AlgebraicGeometry.Flatness.EtaleNeighborhood
public import StacksFrontier.AlgebraicGeometry.Morphisms.Affine.QuasiAffine
public import StacksFrontier.AlgebraicGeometry.Morphisms.Affine.QuasiAffineQuasiFinite
public import StacksFrontier.AlgebraicGeometry.Morphisms.FiniteLocallyFree.Representability
public import StacksCore.Tactic.StacksAttribute

/-!
# Internal homs between finite étale schemes

For finite étale schemes `U` and `V` over a scheme `X`, the functor sending an `X`-scheme `T` to
the morphisms `U ×_X T ⟶ V` over `X` is represented by a finite étale scheme over `X`. In other
words the category of finite étale coverings of `X` has internal homs, and the representing
object is compatible with arbitrary base change because the representation is an isomorphism of
functors on the whole slice category.

## Main results

* `Stacks.FundamentalGroup.exists_finiteEtale_internalHom`: **Stacks Tag 0BL7**, the existence
  of the internal hom as a finite étale scheme over the base, together with the natural
  isomorphism exhibiting it.

## Implementation notes

Products in `Over X` are fibre products over `X`, and the asserted equality of morphism sets,
including its compatibility with arbitrary base change, is expressed as a natural isomorphism
of functors on `(Over X)ᵒᵖ`.

## References

* [Stacks Project, Tag 0BL7](https://stacks.math.columbia.edu/tag/0BL7)
-/

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u v w

namespace Stacks.FundamentalGroup

/-! ### Products in a slice category of schemes against fibre products -/

private lemma overProdMapLeft {S : Scheme.{u}} {A B C D : Over S}
    (a : A ⟶ C) (b : B ⟶ D) :
    (Over.prodLeftIsoPullback A B).inv ≫ (prod.map a b).left ≫
      (Over.prodLeftIsoPullback C D).hom =
    pullback.map A.hom B.hom C.hom D.hom a.left b.left (𝟙 S)
      (by simp) (by simp) := by
  apply pullback.hom_ext
  · simp only [Category.assoc, Over.prodLeftIsoPullback_hom_fst,
      pullback.lift_fst]
    rw [← Over.comp_left, prod.map_fst, Over.comp_left]
    simp
  · simp only [Category.assoc, Over.prodLeftIsoPullback_hom_snd,
      pullback.lift_snd]
    rw [← Over.comp_left, prod.map_snd, Over.comp_left]
    simp

private lemma overProdMapLeft_hom {S : Scheme.{u}} {A B C D : Over S}
    (a : A ⟶ C) (b : B ⟶ D) :
    (prod.map a b).left ≫ (Over.prodLeftIsoPullback C D).hom =
      (Over.prodLeftIsoPullback A B).hom ≫
      pullback.map A.hom B.hom C.hom D.hom a.left b.left (𝟙 S)
          (by simp) (by simp) := by
  calc
    (prod.map a b).left ≫ (Over.prodLeftIsoPullback C D).hom =
        ((Over.prodLeftIsoPullback A B).hom ≫
          (Over.prodLeftIsoPullback A B).inv) ≫ (prod.map a b).left ≫
            (Over.prodLeftIsoPullback C D).hom := by simp
    _ = (Over.prodLeftIsoPullback A B).hom ≫
          pullback.map A.hom B.hom C.hom D.hom a.left b.left (𝟙 S)
            (by simp) (by simp) := by
      rw [Category.assoc, overProdMapLeft]

private lemma overProdFunctorObjObj_left_eqToIso {S : Scheme.{u}} (A B : Over S) :
    eqToIso (congrArg Over.left (Limits.prod.functor_obj_obj A B)) =
      Iso.refl ((A ⨯ B).left) := by
  have hp : ((Limits.prod.functor.obj A).obj B).left = (A ⨯ B).left :=
    congrArg Over.left (Limits.prod.functor_obj_obj A B)
  cases Subsingleton.elim hp (by rfl)
  rfl

private lemma pullbackLeftPullbackSndIso_natural {X T : Scheme.{u}}
    (g : T ⟶ X) {U : Scheme.{u}} (p : U ⟶ X) {A B : Over T} (f : A ⟶ B) :
    let m₁ := pullback.map p (A.hom ≫ g) p (B.hom ≫ g) (𝟙 U) f.left (𝟙 X)
        (by simp) (by simpa [Category.assoc] using f.w_assoc g)
    let m₂ := pullback.map (pullback.snd p g) A.hom (pullback.snd p g) B.hom
        (𝟙 (pullback p g)) f.left (𝟙 T) (by simp) (by simpa using f.w)
    m₁ ≫ (pullbackLeftPullbackSndIso p g B.hom).inv =
    (pullbackLeftPullbackSndIso p g A.hom).inv ≫ m₂ := by
  dsimp only
  let m₁ := pullback.map p (A.hom ≫ g) p (B.hom ≫ g) (𝟙 U) f.left (𝟙 X)
    (by simp) (by simp)
  let m₂ := pullback.map (pullback.snd p g) A.hom (pullback.snd p g) B.hom
    (𝟙 (pullback p g)) f.left (𝟙 T) (by simp) (by simp)
  show m₁ ≫ (pullbackLeftPullbackSndIso p g B.hom).inv =
    (pullbackLeftPullbackSndIso p g A.hom).inv ≫ m₂
  have hA := pullbackLeftPullbackSndIso_inv_fst_snd p g A.hom
  have hB := pullbackLeftPullbackSndIso_inv_fst_snd p g B.hom
  have hA' := pullbackLeftPullbackSndIso_inv_snd_snd p g A.hom
  have hB' := pullbackLeftPullbackSndIso_inv_snd_snd p g B.hom
  have hf : f.left ≫ B.hom = A.hom := f.w
  have hm₁snd : m₁ ≫ pullback.snd p (B.hom ≫ g) =
      pullback.snd p (A.hom ≫ g) ≫ f.left := by
    dsimp [m₁, pullback.map]
    rw [pullback.lift_snd]
  have hm₂fst : m₂ ≫ pullback.fst (pullback.snd p g) B.hom =
      pullback.fst (pullback.snd p g) A.hom ≫ 𝟙 (pullback p g) := by
    dsimp [m₂, pullback.map]
    rw [pullback.lift_fst]
  have hm₂snd : m₂ ≫ pullback.snd (pullback.snd p g) B.hom =
      pullback.snd (pullback.snd p g) A.hom ≫ f.left := by
    dsimp [m₂, pullback.map]
    rw [pullback.lift_snd]
  apply pullback.hom_ext
  · apply pullback.hom_ext
    · simp only [Category.assoc, pullbackLeftPullbackSndIso_inv_fst,
        m₁, m₂, pullback.map, pullback.lift_fst, Category.comp_id]
    · calc
        m₁ ≫ (pullbackLeftPullbackSndIso p g B.hom).inv ≫
              pullback.fst (pullback.snd p g) B.hom ≫ pullback.snd p g =
            m₁ ≫ pullback.snd p (B.hom ≫ g) ≫ B.hom := by
          simpa only [Category.assoc] using congrArg
            (fun k : pullback p (B.hom ≫ g) ⟶ T => m₁ ≫ k) hB
        _ = pullback.snd p (A.hom ≫ g) ≫ A.hom := by
          calc
            _ = pullback.snd p (A.hom ≫ g) ≫ f.left ≫ B.hom := by
              simpa only [Category.assoc] using
                congrArg (fun k => k ≫ B.hom) hm₁snd
            _ = pullback.snd p (A.hom ≫ g) ≫ A.hom := by rw [hf]
        _ = (pullbackLeftPullbackSndIso p g A.hom).inv ≫ m₂ ≫
              pullback.fst (pullback.snd p g) B.hom ≫ pullback.snd p g := by
          calc
            _ = (pullbackLeftPullbackSndIso p g A.hom).inv ≫
                  pullback.fst (pullback.snd p g) A.hom ≫ pullback.snd p g := hA.symm
            _ = (pullbackLeftPullbackSndIso p g A.hom).inv ≫ m₂ ≫
                  pullback.fst (pullback.snd p g) B.hom ≫ pullback.snd p g := by
              simpa only [Category.assoc, Category.id_comp] using
                congrArg (fun k => (pullbackLeftPullbackSndIso p g A.hom).inv ≫
                  k ≫ pullback.snd p g) hm₂fst.symm
  · calc
      m₁ ≫ (pullbackLeftPullbackSndIso p g B.hom).inv ≫
            pullback.snd (pullback.snd p g) B.hom =
          m₁ ≫ pullback.snd p (B.hom ≫ g) := by
        simpa only [Category.assoc] using congrArg (fun k => m₁ ≫ k) hB'
      _ = pullback.snd p (A.hom ≫ g) ≫ f.left := hm₁snd
      _ = (pullbackLeftPullbackSndIso p g A.hom).inv ≫ m₂ ≫
            pullback.snd (pullback.snd p g) B.hom := by
        calc
          _ = (pullbackLeftPullbackSndIso p g A.hom).inv ≫
                pullback.snd (pullback.snd p g) A.hom ≫ f.left := by
            simpa only [Category.assoc] using
              congrArg (fun k => k ≫ f.left) hA'.symm
          _ = (pullbackLeftPullbackSndIso p g A.hom).inv ≫ m₂ ≫
                pullback.snd (pullback.snd p g) B.hom := by
            simpa only [Category.assoc] using congrArg
              (fun k => (pullbackLeftPullbackSndIso p g A.hom).inv ≫ k) hm₂snd.symm

private noncomputable def overMapProdComparison {X T : Scheme.{u}} (g : T ⟶ X)
    (U : Over X) :
    Over.map g ⋙ Limits.prod.functor.obj U ≅
      Limits.prod.functor.obj ((Over.pullback g).obj U) ⋙ Over.map g := by
  let UT := (Over.pullback g).obj U
  let e₁ (A : Over T) :
      ((Limits.prod.functor.obj U).obj ((Over.map g).obj A)).left ≅
        pullback U.hom ((Over.map g).obj A).hom :=
    eqToIso (congrArg Over.left (Limits.prod.functor_obj_obj U ((Over.map g).obj A))) ≪≫
      Over.prodLeftIsoPullback U ((Over.map g).obj A)
  let e₂ (A : Over T) :
      ((Limits.prod.functor.obj UT).obj A).left ≅ pullback UT.hom A.hom :=
    eqToIso (congrArg Over.left (Limits.prod.functor_obj_obj UT A)) ≪≫
      Over.prodLeftIsoPullback UT A
  let α (A : Over T) := pullbackLeftPullbackSndIso U.hom g A.hom
  let e (A : Over T) := e₁ A ≪≫ (α A).symm ≪≫ (e₂ A).symm
  have he₁iso (A : Over T) :
      e₁ A = Over.prodLeftIsoPullback U ((Over.map g).obj A) := by
    change (eqToIso (congrArg Over.left
      (Limits.prod.functor_obj_obj U ((Over.map g).obj A))) ≪≫
        Over.prodLeftIsoPullback U ((Over.map g).obj A)) = _
    rw [overProdFunctorObjObj_left_eqToIso]
    exact Iso.refl_trans _
  have he₂iso (A : Over T) :
      e₂ A = Over.prodLeftIsoPullback UT A := by
    change (eqToIso (congrArg Over.left (Limits.prod.functor_obj_obj UT A)) ≪≫
      Over.prodLeftIsoPullback UT A) = _
    rw [overProdFunctorObjObj_left_eqToIso]
    exact Iso.refl_trans _
  let hL (A : Over T) :
      ((Over.map g ⋙ Limits.prod.functor.obj U).obj A).left =
        ((Limits.prod.functor.obj U).obj ((Over.map g).obj A)).left := rfl
  let hR (A : Over T) :
      ((Limits.prod.functor.obj UT ⋙ Over.map g).obj A).left =
        ((Over.map g).obj ((Limits.prod.functor.obj UT).obj A)).left := rfl
  let e' (A : Over T) :
      ((Over.map g ⋙ Limits.prod.functor.obj U).obj A).left ≅
        ((Limits.prod.functor.obj UT ⋙ Over.map g).obj A).left :=
    eqToIso (hL A) ≪≫ e A ≪≫ (eqToIso (hR A)).symm
  have hLid (A : Over T) : eqToHom (hL A) = 𝟙 _ := by
    have hp : hL A = (by rfl) := Subsingleton.elim _ _
    rw [hp]
    rfl
  have hRidSymm (A : Over T) : eqToHom (hR A).symm = 𝟙 _ := by
    have hp : hR A = (by rfl) := Subsingleton.elim _ _
    rw [hp]
    rfl
  refine NatIso.ofComponents (fun A : Over T => ?_) ?_
  · have hprodT : (prod.snd (X := UT)).left ≫ A.hom = (UT ⨯ A).hom :=
      Over.w (prod.snd (X := UT))
    have hprodX : (prod.snd (X := U)).left ≫ ((Over.map g).obj A).hom =
        (U ⨯ (Over.map g).obj A).hom := Over.w (prod.snd (X := U))
    have he₂' : (Over.prodLeftIsoPullback UT A).inv ≫ (UT ⨯ A).hom =
        pullback.snd UT.hom A.hom ≫ A.hom := by
      rw [← hprodT]
      change ((Over.prodLeftIsoPullback UT A).inv ≫
        (prod.snd (X := UT)).left) ≫ A.hom = _
      rw [Over.prodLeftIsoPullback_inv_snd]
    have hassoc : (α A).inv ≫
        pullback.snd UT.hom A.hom = pullback.snd U.hom (A.hom ≫ g) := by
      simpa only [α, UT, Over.pullback_obj_hom] using
        pullbackLeftPullbackSndIso_inv_snd_snd U.hom g A.hom
    have he₁' : (Over.prodLeftIsoPullback U ((Over.map g).obj A)).hom ≫
        pullback.snd U.hom (A.hom ≫ g) = (prod.snd (X := U)).left :=
      Over.prodLeftIsoPullback_hom_snd U ((Over.map g).obj A)
    have hbase' : (Over.prodLeftIsoPullback U ((Over.map g).obj A)).hom ≫
        (α A).inv ≫ (Over.prodLeftIsoPullback UT A).inv ≫
        (UT ⨯ A).hom ≫ g =
        (U ⨯ (Over.map g).obj A).hom := by
      calc
        _ = (Over.prodLeftIsoPullback U ((Over.map g).obj A)).hom ≫ (α A).inv ≫
              ((Over.prodLeftIsoPullback UT A).inv ≫ (UT ⨯ A).hom) ≫ g := by
          simp only [Category.assoc]
        _ = (Over.prodLeftIsoPullback U ((Over.map g).obj A)).hom ≫ (α A).inv ≫
              (pullback.snd UT.hom A.hom ≫ A.hom) ≫ g := by
          rw [he₂']
        _ = (Over.prodLeftIsoPullback U ((Over.map g).obj A)).hom ≫
              pullback.snd U.hom (A.hom ≫ g) ≫ (A.hom ≫ g) := by
          simpa [Category.assoc] using
            congrArg (fun h =>
              (Over.prodLeftIsoPullback U ((Over.map g).obj A)).hom ≫ h ≫ A.hom ≫ g)
              hassoc
        _ = (prod.snd (X := U)).left ≫ A.hom ≫ g := by
          simpa only [Category.assoc] using
            congrArg (fun k => k ≫ A.hom ≫ g) he₁'
        _ = (U ⨯ (Over.map g).obj A).hom := by
          simpa [Over.map_obj_hom, Category.assoc] using hprodX
    have hbase : (e A).hom ≫ (UT ⨯ A).hom ≫ g =
        (U ⨯ (Over.map g).obj A).hom := by
      change (e₁ A ≪≫ (α A).symm ≪≫ (e₂ A).symm).hom ≫
        (UT ⨯ A).hom ≫ g = (U ⨯ (Over.map g).obj A).hom
      simp only [he₁iso A, he₂iso A]
      exact hbase'
    refine Over.isoMk (e' A) ?_
    change eqToHom (hL A) ≫ (e A).hom ≫ eqToHom (hR A).symm ≫
        (UT ⨯ A).hom ≫ g = (U ⨯ (Over.map g).obj A).hom
    rw [hLid A, hRidSymm A]
    simpa [Over.map_obj_hom, Category.assoc] using hbase
  · intro A B f
    cases hL A
    cases hL B
    cases hR A
    cases hR B
    apply Over.OverMorphism.ext
    dsimp only [Functor.comp_map, Functor.comp_obj]
    let m₁ := pullback.map U.hom (A.hom ≫ g) U.hom (B.hom ≫ g)
      (𝟙 U.left) f.left (𝟙 X) (by simp) (by simp)
    let m₂ := pullback.map UT.hom A.hom UT.hom B.hom
      (𝟙 UT.left) f.left (𝟙 T) (by simp) (by simp)
    have hprod₁ :
        ((Limits.prod.functor.obj U).map ((Over.map g).map f)).left ≫ (e₁ B).hom =
          (e₁ A).hom ≫ m₁ := by
      have hmap : ((Over.map g).map f).left = f.left := rfl
      rw [he₁iso A, he₁iso B]
      change (prod.map (𝟙 U) ((Over.map g).map f)).left ≫
          (Over.prodLeftIsoPullback U ((Over.map g).obj B)).hom =
        (Over.prodLeftIsoPullback U ((Over.map g).obj A)).hom ≫ m₁
      simpa [hmap] using overProdMapLeft_hom (𝟙 U) ((Over.map g).map f)
    have hprod₂ :
        (e₂ A).inv ≫ ((Limits.prod.functor.obj UT).map f).left ≫ (e₂ B).hom = m₂ := by
      rw [he₂iso A, he₂iso B]
      change (Over.prodLeftIsoPullback UT A).inv ≫
          (prod.map (𝟙 UT) f).left ≫ (Over.prodLeftIsoPullback UT B).hom = m₂
      simpa [m₂] using overProdMapLeft (𝟙 UT) f
    have hprod₂' :
        (e₂ A).inv ≫ ((Over.map g).map ((Limits.prod.functor.obj UT).map f)).left =
          m₂ ≫ (e₂ B).inv := by
      have hmap : ((Over.map g).map ((Limits.prod.functor.obj UT).map f)).left =
          ((Limits.prod.functor.obj UT).map f).left := rfl
      rw [hmap]
      apply (cancel_mono (e₂ B).hom).1
      simpa [Category.assoc, Over.map, Limits.prod.functor_obj_obj] using hprod₂
    have hα := pullbackLeftPullbackSndIso_natural g U.hom f
    change ((Limits.prod.functor.obj U).map ((Over.map g).map f)).left ≫
        (e B).hom = (e A).hom ≫
          ((Over.map g).map ((Limits.prod.functor.obj UT).map f)).left
    simp only [e, Iso.trans_hom, Iso.symm_hom]
    rw [← Category.assoc, hprod₁]
    have hmid : m₁ ≫ (α B).inv ≫ (e₂ B).inv =
        (α A).inv ≫ (e₂ A).inv ≫
          ((Over.map g).map ((Limits.prod.functor.obj UT).map f)).left := by
      calc
        m₁ ≫ (α B).inv ≫ (e₂ B).inv =
            (α A).inv ≫ m₂ ≫ (e₂ B).inv := by
          simpa only [m₁, m₂, α, UT, Over.pullback_obj_hom, Over.pullback_obj_left,
            Category.assoc] using congrArg
            (fun k => k ≫ (e₂ B).inv) hα
        _ = (α A).inv ≫ (e₂ A).inv ≫
            ((Over.map g).map ((Limits.prod.functor.obj UT).map f)).left := by
          simpa only [Category.assoc] using congrArg
            (fun k => (α A).inv ≫ k) hprod₂'.symm
    simpa only [Category.assoc] using congrArg (fun k => (e₁ A).hom ≫ k) hmid

private noncomputable def adjunctionYonedaIso {C : Type u} {D : Type v}
    [Category.{w} C] [Category.{w} D] {L : C ⥤ D} {R : D ⥤ C}
    (a : L ⊣ R) (Y : D) :
    yoneda.obj (R.obj Y) ≅ L.op ⋙ yoneda.obj Y :=
  NatIso.ofComponents (fun X => Equiv.toIso (a.homEquiv X.unop Y).symm) (by
    intro X X' f
    ext g
    change (a.homEquiv _ _).symm (f.unop ≫ g) =
      L.map f.unop ≫ (a.homEquiv _ _).symm g
    exact a.homEquiv_naturality_left_symm f.unop g)

/-- The inclusion of the unique summand of a constant `PUnit`-indexed coproduct, followed by
`coproductUniqueIso`, is the identity. -/
private lemma coproductUniqueIso_ι_punit (A : Scheme.{u}) :
    Sigma.ι (fun _ : PUnit => A) PUnit.unit ≫
      (coproductUniqueIso (fun _ : PUnit => A)).hom = 𝟙 A := by
  simp

/-- Pulling back a finite coproduct of copies of the base gives the corresponding
coproduct of copies of any test scheme. -/
private noncomputable def splitPullbackIso {S : Scheme.{u}} {n : ℕ} (A : Over S) :
    (∐ fun _ : Fin n => A.left) ≅
      pullback (Sigma.desc (fun _ : Fin n => 𝟙 S)) A.hom := by
  let pbOne := pullback (𝟙 S) A.hom
  let ePb : A.left ≅ pbOne := (asIso (pullback.snd (𝟙 S) A.hom)).symm
  let idx : Fin n → Fin n × PUnit := fun i => (i, PUnit.unit)
  let k : (∐ fun _ : Fin n => A.left) ⟶
      ∐ fun p : Fin n × PUnit => pbOne :=
    Sigma.map' idx (fun _ => ePb.hom)
  let kInv : (∐ fun p : Fin n × PUnit => pbOne) ⟶
      ∐ fun _ : Fin n => A.left :=
    Sigma.map' Prod.fst (fun _ => ePb.inv)
  have hk₁ : k ≫ kInv = 𝟙 _ := by
    apply Sigma.hom_ext
    intro i
    simp [k, kInv, idx, Sigma.map'_comp_map']
  have hk₂ : kInv ≫ k = 𝟙 _ := by
    apply Sigma.hom_ext
    rintro ⟨i, ⟨⟩⟩
    simp [k, kInv, idx, Sigma.map'_comp_map']
  let kIso : (∐ fun _ : Fin n => A.left) ≅
      ∐ fun p : Fin n × PUnit => pbOne := ⟨k, kInv, hk₁, hk₂⟩
  let gObjs : PUnit → Scheme.{u} := fun _ => A.left
  let g : (j : PUnit) → gObjs j ⟶ S := fun _ => A.hom
  let dPair : (∐ fun p : Fin n × PUnit => pbOne) ⟶
      pullback (Sigma.desc (fun _ : Fin n => 𝟙 S)) (Sigma.desc g) :=
    Sigma.desc (fun p : Fin n × PUnit =>
      pullback.map (𝟙 S) A.hom (Sigma.desc (fun _ : Fin n => 𝟙 S)) (Sigma.desc g)
        (Sigma.ι (fun _ : Fin n => S) p.1) (Sigma.ι gObjs p.2) (𝟙 S)
        (by simp) (by simp [g, gObjs]))
  have hdPair : IsIso dPair := by
    dsimp [dPair, pbOne]
    exact FinitaryPreExtensive.isIso_sigmaDesc_map
      (fun _ : Fin n => 𝟙 S) g
  let eB : (∐ gObjs) ≅ A.left := coproductUniqueIso gObjs
  have hB : Sigma.desc g = eB.hom ≫ A.hom := by
    apply Sigma.hom_ext
    intro j
    simp [g, gObjs, eB]
  let pmap := pullback.map (Sigma.desc (fun _ : Fin n => 𝟙 S)) (Sigma.desc g)
      (Sigma.desc (fun _ : Fin n => 𝟙 S)) A.hom (𝟙 _) eB.hom (𝟙 S)
      (by simp) (by simp [hB])
  haveI : IsIso pmap := by infer_instance
  let tIso : pullback (Sigma.desc (fun _ : Fin n => 𝟙 S)) (Sigma.desc g) ≅
      pullback (Sigma.desc (fun _ : Fin n => 𝟙 S)) A.hom := asIso pmap
  exact kIso ≪≫ asIso dPair ≪≫ tIso

private lemma splitPullbackIso_fst {S : Scheme.{u}} {n : ℕ} (A : Over S)
    (i : Fin n) :
    Sigma.ι (fun _ : Fin n => A.left) i ≫ (splitPullbackIso A).hom ≫
      pullback.fst (Sigma.desc (fun _ : Fin n => 𝟙 S)) A.hom =
    A.hom ≫ Sigma.ι (fun _ : Fin n => S) i := by
  simp [splitPullbackIso, Category.assoc, pullback.map]
  simp only [← Category.assoc, pullback.lift_fst]
  simpa [Category.assoc] using congrArg
    (fun k => k ≫ Sigma.ι (fun _ : Fin n => S) i)
      (pullback.condition (f := 𝟙 S) (g := A.hom))

private lemma splitPullbackIso_snd {S : Scheme.{u}} {n : ℕ} (A : Over S)
    (i : Fin n) :
    Sigma.ι (fun _ : Fin n => A.left) i ≫ (splitPullbackIso A).hom ≫
      pullback.snd (Sigma.desc (fun _ : Fin n => 𝟙 S)) A.hom =
    𝟙 A.left := by
  simp only [splitPullbackIso, Iso.symm_hom, asIso_inv, Iso.symm_inv, asIso_hom, pullback.map,
    Category.comp_id, Iso.trans_hom, Category.assoc, Sigma.ι_comp_map'_assoc, colimit.ι_desc_assoc,
    Discrete.functor_obj_eq_as, Cofan.mk_pt, Cofan.mk_ι_app, IsIso.inv_comp_eq]
  simp only [← Category.assoc, pullback.lift_snd]
  rw [Category.assoc (f := pullback.snd (𝟙 S) A.hom)
    (g := Sigma.ι (fun _ : PUnit => A.left) PUnit.unit)
    (h := (coproductUniqueIso (fun _ : PUnit => A.left)).hom), coproductUniqueIso_ι_punit]
  simp

private abbrev overSigmaFunctor {S : Scheme.{u}} {n : ℕ} :
    Over S ⥤ Over S where
  obj A := Over.mk (Sigma.desc (fun _ : Fin n => A.hom))
  map f := Over.homMk (Sigma.map' (fun i : Fin n => i) (fun _ => f.left)) (by
    apply Sigma.hom_ext
    intro i
    simp [Over.w f])
  map_id A := by
    apply Over.OverMorphism.ext
    apply Sigma.hom_ext
    intro i
    simp
  map_comp f g := by
    apply Over.OverMorphism.ext
    apply Sigma.hom_ext
    intro i
    simp [Category.assoc]

private noncomputable def splitPullbackOverIso {S : Scheme.{u}} {n : ℕ}
    (A : Over S) :
    Over.mk (Sigma.desc (fun _ : Fin n => A.hom)) ≅
      (Over.mk (Sigma.desc (fun _ : Fin n => 𝟙 S))) ⨯ A := by
  let e := splitPullbackIso A ≪≫
    (Over.prodLeftIsoPullback (Over.mk (Sigma.desc (fun _ : Fin n => 𝟙 S))) A).symm
  refine Over.isoMk e ?_
  have he₂ :
      (Over.prodLeftIsoPullback (Over.mk (Sigma.desc (fun _ : Fin n => 𝟙 S))) A).inv ≫
        ((Over.mk (Sigma.desc (fun _ : Fin n => 𝟙 S)) ⨯ A).hom) =
      pullback.snd (Sigma.desc (fun _ : Fin n => 𝟙 S)) A.hom ≫ A.hom := by
    rw [← Over.w (prod.snd (X := Over.mk (Sigma.desc (fun _ : Fin n => 𝟙 S))))]
    change ((Over.prodLeftIsoPullback
      (Over.mk (Sigma.desc (fun _ : Fin n => 𝟙 S))) A).inv ≫
        (prod.snd (X := Over.mk (Sigma.desc (fun _ : Fin n => 𝟙 S)))).left) ≫ A.hom = _
    rw [Over.prodLeftIsoPullback_inv_snd]
    change pullback.snd (Sigma.desc (fun _ : Fin n => 𝟙 S)) A.hom ≫ A.hom = _
    rfl
  apply Sigma.hom_ext
  intro i
  have hsp : Sigma.ι (fun _ : Fin n => A.left) i ≫
      (splitPullbackIso A).hom ≫
      pullback.snd (Sigma.desc (fun _ : Fin n => 𝟙 S)) A.hom ≫ A.hom =
      Sigma.ι (fun _ : Fin n => A.left) i ≫ Sigma.desc (fun _ : Fin n => A.hom) := by
    simpa only [Category.assoc, Sigma.ι_desc, Category.id_comp] using
      congrArg (fun f => f ≫ A.hom) (splitPullbackIso_snd A i)
  change Sigma.ι (fun _ : Fin n => A.left) i ≫ e.hom ≫
      (Over.mk (Sigma.desc (fun _ : Fin n => 𝟙 S)) ⨯ A).hom =
    Sigma.ι (fun _ : Fin n => A.left) i ≫ Sigma.desc (fun _ : Fin n => A.hom)
  rw [show e.hom = (splitPullbackIso A).hom ≫
      (Over.prodLeftIsoPullback (Over.mk (Sigma.desc (fun _ : Fin n => 𝟙 S))) A).inv by rfl,
    Category.assoc, he₂]
  exact hsp

private noncomputable def overSigmaι {S : Scheme.{u}} {n : ℕ} (A : Over S)
    (i : Fin n) : A ⟶ (overSigmaFunctor (n := n)).obj A :=
  Over.homMk (Sigma.ι (fun _ : Fin n => A.left) i) (by simp)

private noncomputable def splitBaseι {S : Scheme.{u}} {n : ℕ} (A : Over S)
    (i : Fin n) : A ⟶ Over.mk (Sigma.desc (fun _ : Fin n => 𝟙 S)) :=
  Over.homMk (A.hom ≫ Sigma.ι (fun _ : Fin n => S) i) (by
    simp [Category.assoc])

private lemma splitPullbackOverIso_ι {S : Scheme.{u}} {n : ℕ} (A : Over S)
    (i : Fin n) :
    overSigmaι A i ≫ (splitPullbackOverIso A).hom =
      prod.lift (splitBaseι A i) (𝟙 A) := by
  apply Over.OverMorphism.ext
  apply (cancel_mono (Over.prodLeftIsoPullback
    (Over.mk (Sigma.desc (fun _ : Fin n => 𝟙 S))) A).hom).1
  apply pullback.hom_ext
  · conv_rhs =>
      rw [Category.assoc, Over.prodLeftIsoPullback_hom_fst]
      rw [← Over.comp_left, prod.lift_fst]
    simpa [splitPullbackOverIso, overSigmaι, splitBaseι, Category.assoc,
      Over.comp_left] using splitPullbackIso_fst A i
  · conv_rhs =>
      rw [Category.assoc, Over.prodLeftIsoPullback_hom_snd]
      rw [← Over.comp_left, prod.lift_snd]
    simpa [splitPullbackOverIso, overSigmaι, Category.assoc,
      Over.comp_left] using splitPullbackIso_snd A i

private noncomputable def splitPullbackOverIsoNat {S : Scheme.{u}} {n : ℕ} :
    overSigmaFunctor (S := S) (n := n) ≅
      Limits.prod.functor.obj (Over.mk (Sigma.desc (fun _ : Fin n => 𝟙 S))) := by
  refine NatIso.ofComponents (fun A => ?_) ?_
  · change Over.mk (Sigma.desc (fun _ : Fin n => A.hom)) ≅
      (Over.mk (Sigma.desc (fun _ : Fin n => 𝟙 S)) ⨯ A)
    exact splitPullbackOverIso A
  · intro A A' f
    apply Over.OverMorphism.ext
    apply Sigma.hom_ext
    intro i
    change Sigma.ι (fun _ : Fin n => A.left) i ≫
        Sigma.map' (fun j : Fin n => j) (fun _ => f.left) ≫
          (splitPullbackOverIso A').hom.left =
      Sigma.ι (fun _ : Fin n => A.left) i ≫ (splitPullbackOverIso A).hom.left ≫
        (prod.map (𝟙 (Over.mk (Sigma.desc (fun _ : Fin n => 𝟙 S)))) f).left
    have hcop : Sigma.ι (fun _ : Fin n => A.left) i ≫
        Sigma.map' (fun j : Fin n => j) (fun _ => f.left) =
          f.left ≫ Sigma.ι (fun _ : Fin n => A'.left) i :=
      Sigma.ι_comp_map' (p := fun j : Fin n => j) (q := fun _ => f.left) i
    have hι : overSigmaι A i ≫ (overSigmaFunctor (n := n)).map f =
        f ≫ overSigmaι A' i := by
      apply Over.OverMorphism.ext
      exact hcop
    have hBase : f ≫ splitBaseι A' i = splitBaseι A i := by
      apply Over.OverMorphism.ext
      change f.left ≫ (A'.hom ≫ Sigma.ι (fun _ : Fin n => S) i) =
        A.hom ≫ Sigma.ι (fun _ : Fin n => S) i
      rw [← Category.assoc, Over.w f]
    have hLift : f ≫ prod.lift (splitBaseι A' i) (𝟙 A') =
        prod.lift (splitBaseι A i) f := by
      apply prod.hom_ext
      · simpa only [prod.lift_fst, Category.assoc] using hBase
      · simp
    have hNatι : overSigmaι A i ≫ (overSigmaFunctor (n := n)).map f ≫
        (splitPullbackOverIso A').hom = overSigmaι A i ≫
          (splitPullbackOverIso A).hom ≫
            prod.map (𝟙 (Over.mk (Sigma.desc (fun _ : Fin n => 𝟙 S)))) f := by
      calc
        _ = (f ≫ overSigmaι A' i) ≫ (splitPullbackOverIso A').hom := by
          calc
            _ = (overSigmaι A i ≫ (overSigmaFunctor (n := n)).map f) ≫
                (splitPullbackOverIso A').hom := by simp only [Category.assoc]
            _ = _ := congrArg
              (fun k : A ⟶ (overSigmaFunctor (n := n)).obj A' =>
                k ≫ (splitPullbackOverIso A').hom) hι
        _ = f ≫ (overSigmaι A' i ≫ (splitPullbackOverIso A').hom) := by
          simp only [Category.assoc]
        _ = f ≫ prod.lift (splitBaseι A' i) (𝟙 A') :=
          congrArg (fun k => f ≫ k) (splitPullbackOverIso_ι A' i)
        _ = prod.lift (splitBaseι A i) (𝟙 A) ≫
            prod.map (𝟙 (Over.mk (Sigma.desc (fun _ : Fin n => 𝟙 S)))) f :=
          hLift.trans (prod.lift_map (splitBaseι A i) (𝟙 A)
            (𝟙 (Over.mk (Sigma.desc (fun _ : Fin n => 𝟙 S)))) f).symm
        _ = (overSigmaι A i ≫ (splitPullbackOverIso A).hom) ≫
            prod.map (𝟙 (Over.mk (Sigma.desc (fun _ : Fin n => 𝟙 S)))) f := by
          rw [← splitPullbackOverIso_ι]
        _ = overSigmaι A i ≫ (splitPullbackOverIso A).hom ≫
            prod.map (𝟙 (Over.mk (Sigma.desc (fun _ : Fin n => 𝟙 S)))) f := by
          simp only [Category.assoc]
    have hleft := congrArg Over.Hom.left hNatι
    dsimp only [overSigmaι, overSigmaFunctor, Over.homMk] at hleft
    exact hleft

private noncomputable def piSumIso {S : Scheme.{u}} (A : Over S) {n : ℕ} :
    (∏ᶜ fun _ : Fin n ⊕ PUnit.{1} => A) ≅ A ⨯ (∏ᶜ fun _ : Fin n => A) where
  hom := prod.lift
    (Pi.π (fun _ : Fin n ⊕ PUnit.{1} => A) (Sum.inr PUnit.unit))
    (Pi.lift fun i => Pi.π (fun _ : Fin n ⊕ PUnit.{1} => A) (Sum.inl i))
  inv := Pi.lift (Sum.elim
    (fun i => prod.snd ≫ Pi.π (fun _ : Fin n => A) i)
    (fun _ => prod.fst))
  hom_inv_id := by
    apply Pi.hom_ext
    intro i
    cases i with
    | inl i => simp [Category.assoc]
    | inr i => cases i; simp [Category.assoc]
  inv_hom_id := by
    apply prod.hom_ext
    · simp
    · apply Pi.hom_ext
      intro i
      simp [Category.assoc]

/-- `Fin (n + 1)` is equivalent to `Fin n ⊕ PUnit`, with `0` sent to the right summand and
`i.succ` to `Sum.inl i`. -/
private noncomputable def finSuccSumEquiv (n : ℕ) : Fin (n + 1) ≃ Fin n ⊕ PUnit.{1} where
  toFun := Fin.cases (Sum.inr PUnit.unit) (fun i => Sum.inl i)
  invFun := Sum.elim Fin.succ (fun _ => 0)
  left_inv := by
    intro i
    induction i using Fin.cases with
    | zero => simp
    | succ i => simp
  right_inv := by
    intro i
    cases i with
    | inl i => simp
    | inr i => cases i; simp

private noncomputable def piFinSuccIso {S : Scheme.{u}} (A : Over S) (n : ℕ) :
    (∏ᶜ fun _ : Fin (n + 1) => A) ≅ A ⨯ (∏ᶜ fun _ : Fin n => A) :=
  Pi.whiskerEquiv (finSuccSumEquiv n) (fun _ => Iso.refl A) ≪≫ piSumIso A

attribute [local instance] Stacks.Morphisms.isFinite_respectsIso

private instance etale_respectsIso :
    MorphismProperty.RespectsIso (@Etale : MorphismProperty Scheme.{u}) :=
  MorphismProperty.IsStableUnderBaseChange.respectsIso

private lemma piFinZero_hom_isIso {S : Scheme.{u}} (A : Over S) :
    IsIso (∏ᶜ fun _ : Fin 0 => A).hom := by
  let P : Over S := ∏ᶜ fun _ : Fin 0 => A
  have hterm : Limits.IsTerminal P := by
    refine {
      lift := fun Z => Pi.lift (fun i : Fin 0 => Fin.elim0 i)
      fac := ?_
      uniq := ?_ }
    · intro Z i
      exact PEmpty.elim i.as
    · intro Z f hf
      exact Pi.hom_ext f _ (fun i => Fin.elim0 i)
  let e : P ≅ Over.mk (𝟙 S) := hterm.uniqueUpToIso (Over.mkIdTerminal (X := S))
  let eS : P.left ≅ S := Functor.mapIso (Over.forget S) e
  have he : e.hom.left = P.hom := by simpa using Over.w e.hom
  rw [← he]
  exact (inferInstance : IsIso eS.hom)

/-- A morphism property that respects isomorphisms holds for the structure map of `A` as soon as
it holds for that of an isomorphic object `B` of the slice. -/
private lemma hom_of_iso_over {P : MorphismProperty Scheme.{u}} [P.RespectsIso] {S : Scheme.{u}}
    {A B : Over S} (e : A ≅ B) (h : P B.hom) : P A.hom := by
  have : IsIso e.hom.left := inferInstanceAs (IsIso ((Over.forget S).map e.hom))
  rw [← Over.w e.hom]
  exact (P.cancel_left_of_respectsIso _ _).2 h

/-- A base-change stable, composition stable, iso-respecting morphism property is closed under
products in the slice category over `S`. -/
private lemma prod_over_hom {P : MorphismProperty Scheme.{u}} [P.IsStableUnderBaseChange]
    [P.IsMultiplicative] [P.RespectsIso] {S : Scheme.{u}} {A B : Over S}
    (hA : P A.hom) (hB : P B.hom) : P (A ⨯ B).hom := by
  have hfst : P (prod.fst (X := A) (Y := B)).left := by
    rw [← Over.prodLeftIsoPullback_hom_fst A B]
    exact (P.cancel_left_of_respectsIso _ _).2 (P.pullback_fst _ _ hB)
  rw [← Over.w (prod.fst (X := A) (Y := B))]
  exact P.comp_mem _ _ hfst hA

/-- A base-change stable, composition stable, iso-respecting morphism property is closed under
finite products in the slice category over `S`. -/
private lemma pi_over_hom {P : MorphismProperty Scheme.{u}} [P.IsStableUnderBaseChange]
    [P.IsMultiplicative] [P.RespectsIso] {S : Scheme.{u}} {A : Over S}
    (hA : P A.hom) (n : ℕ) : P (∏ᶜ fun _ : Fin n => A).hom := by
  induction n with
  | zero =>
    have := piFinZero_hom_isIso A
    exact P.of_isIso _
  | succ n ih => exact hom_of_iso_over (piFinSuccIso A n) (prod_over_hom hA ih)

private noncomputable def overSigmaHomYonedaIso {S : Scheme.{u}} {n : ℕ}
    (V : Over S) :
    (overSigmaFunctor (S := S) (n := n)).op ⋙ yoneda.obj V ≅
      yoneda.obj (∏ᶜ fun _ : Fin n => V) := by
  classical
  refine NatIso.ofComponents (fun A => Equiv.toIso {
    toFun := fun f => Pi.lift fun i => overSigmaι A.unop i ≫ f
    invFun := fun f => Over.homMk
      (Sigma.desc fun i => f.left ≫ (Pi.π (fun _ : Fin n => V) i).left)
      (by
        apply Sigma.hom_ext
        intro i
        calc
          Sigma.ι (fun _ : Fin n => A.unop.left) i ≫
              Sigma.desc (fun i => f.left ≫ (Pi.π (fun _ : Fin n => V) i).left) ≫ V.hom =
            f.left ≫ (Pi.π (fun _ : Fin n => V) i).left ≫ V.hom := by simp [Category.assoc]
          _ = f.left ≫ (∏ᶜ fun _ : Fin n => V).hom := by
            rw [Over.w (Pi.π (fun _ : Fin n => V) i)]
          _ = A.unop.hom := by rw [Over.w f]
          _ = Sigma.ι (fun _ : Fin n => A.unop.left) i ≫
              Sigma.desc (fun _ : Fin n => A.unop.hom) := by
            symm
            exact Sigma.ι_desc (fun _ : Fin n => A.unop.hom) i)
    left_inv := by
      intro f
      apply Over.OverMorphism.ext
      apply Sigma.hom_ext
      intro i
      change Sigma.ι (fun _ : Fin n => A.unop.left) i ≫
          Sigma.desc (fun j => (Pi.lift (fun k => overSigmaι A.unop k ≫ f)).left ≫
            (Pi.π (fun _ : Fin n => V) j).left) =
        Sigma.ι (fun _ : Fin n => A.unop.left) i ≫ f.left
      rw [Sigma.ι_desc]
      calc
        (Pi.lift (fun k => overSigmaι A.unop k ≫ f)).left ≫
            (Pi.π (fun _ : Fin n => V) i).left =
          (overSigmaι A.unop i ≫ f).left :=
            congrArg Over.Hom.left (Pi.lift_π (fun k => overSigmaι A.unop k ≫ f) i)
        _ = Sigma.ι (fun _ : Fin n => A.unop.left) i ≫ f.left := rfl
    right_inv := by
      intro f
      exact Limits.Fan.IsLimit.hom_ext (Limits.productIsProduct (fun _ : Fin n => V))
        _ _ (by
          intro i
          change (Pi.lift (fun k => overSigmaι A.unop k ≫
              Over.homMk (Sigma.desc fun j => f.left ≫ (Pi.π (fun _ : Fin n => V) j).left) _) ≫
            Pi.π (fun _ : Fin n => V) i) = f ≫ Pi.π (fun _ : Fin n => V) i
          rw [Pi.lift_π]
          apply Over.OverMorphism.ext
          simp [overSigmaι])
  }) ?_
  intro A B f
  ext g
  exact Limits.Fan.IsLimit.hom_ext (Limits.productIsProduct (fun _ : Fin n => V))
    _ _ (by
      intro i
      change (Pi.lift (fun j => overSigmaι B.unop j ≫
          (overSigmaFunctor (n := n)).map f.unop ≫ g) ≫ Pi.π (fun _ : Fin n => V) i) =
        (f.unop ≫ Pi.lift (fun j => overSigmaι A.unop j ≫ g)) ≫
          Pi.π (fun _ : Fin n => V) i
      have hι : overSigmaι B.unop i ≫ overSigmaFunctor.map f.unop =
          f.unop ≫ overSigmaι A.unop i := by
        apply Over.OverMorphism.ext
        change Sigma.ι (fun _ : Fin n => B.unop.left) i ≫
            Sigma.map' (fun j : Fin n => j) (fun _ => f.unop.left) =
          f.unop.left ≫ Sigma.ι (fun _ : Fin n => A.unop.left) i
        rw [Sigma.ι_comp_map']
      rw [Pi.lift_π, ← Category.assoc, hι]
      simp only [Pi.lift_π, Category.assoc])

private noncomputable def splitInternalHomIso {X T : Scheme.{u}} (g : T ⟶ X)
    (U V : Over X) {n : ℕ}
    (e : (Over.pullback g).obj U ≅ Over.mk (Sigma.desc (fun _ : Fin n => 𝟙 T))) :
    (Over.map g).op ⋙
        ((Limits.prod.functor.obj U).op ⋙ yoneda.obj V) ≅
      yoneda.obj (∏ᶜ fun _ : Fin n => (Over.pullback g).obj V) := by
  let L := Over.map g
  let UT := (Over.pullback g).obj U
  let VT := (Over.pullback g).obj V
  let Q : Over T := Over.mk (Sigma.desc (fun _ : Fin n => 𝟙 T))
  let hprod : L.op ⋙ (Limits.prod.functor.obj U).op ≅
      (Limits.prod.functor.obj UT).op ⋙ L.op :=
    (Functor.opComp L (Limits.prod.functor.obj U)).symm ≪≫
      NatIso.op (overMapProdComparison g U).symm ≪≫
      Functor.opComp (Limits.prod.functor.obj UT) L
  let hV : yoneda.obj VT ≅ L.op ⋙ yoneda.obj V :=
    adjunctionYonedaIso (Over.mapPullbackAdj g) V
  let hU : Limits.prod.functor.obj UT ≅ Limits.prod.functor.obj Q :=
    NatIso.ofComponents (fun A => prod.mapIso e (Iso.refl A)) (by
      intro A B f
      apply prod.hom_ext
      · change (prod.map (𝟙 UT) f ≫ prod.map e.hom (𝟙 B)) ≫ prod.fst =
          (prod.map e.hom (𝟙 A) ≫ prod.map (𝟙 Q) f) ≫ prod.fst
        simp only [prod.map_map, Category.id_comp, Category.comp_id, prod.map_fst]
        rw [← Category.assoc, Category.comp_id]
      · change (prod.map (𝟙 UT) f ≫ prod.map e.hom (𝟙 B)) ≫ prod.snd =
          (prod.map e.hom (𝟙 A) ≫ prod.map (𝟙 Q) f) ≫ prod.snd
        simp [prod.map_snd]
        rfl)
  let hSplit := splitPullbackOverIsoNat (S := T) (n := n)
  calc
    L.op ⋙ ((Limits.prod.functor.obj U).op ⋙ yoneda.obj V) ≅
        (L.op ⋙ (Limits.prod.functor.obj U).op) ⋙ yoneda.obj V :=
      Functor.associator _ _ _ |>.symm
    _ ≅ ((Limits.prod.functor.obj UT).op ⋙ L.op) ⋙ yoneda.obj V :=
      Functor.isoWhiskerRight hprod (yoneda.obj V)
    _ ≅ (Limits.prod.functor.obj UT).op ⋙ (L.op ⋙ yoneda.obj V) :=
      Functor.associator _ _ _
    _ ≅ (Limits.prod.functor.obj UT).op ⋙ yoneda.obj VT :=
      Functor.isoWhiskerLeft (Limits.prod.functor.obj UT).op hV.symm
    _ ≅ (Limits.prod.functor.obj Q).op ⋙ yoneda.obj VT :=
      Functor.isoWhiskerRight (NatIso.op hU.symm) (yoneda.obj VT)
    _ ≅ (overSigmaFunctor (S := T) (n := n)).op ⋙ yoneda.obj VT :=
      Functor.isoWhiskerRight (NatIso.op hSplit) (yoneda.obj VT)
    _ ≅ yoneda.obj (∏ᶜ fun _ : Fin n => VT) := overSigmaHomYonedaIso VT

/-! ### Locality on the base and representability of relative homs -/

/-- **Stacks Project, Tag 02VN.** Étale morphisms of schemes are local on the base for the fpqc
topology. -/
private theorem etale_isLocalAtTarget_fpqc :
    MorphismProperty.IsLocalAtTarget (@Etale : MorphismProperty Scheme.{u})
      Scheme.fpqcPrecoverage :=
  have : IsZariskiLocalAtTarget (@Etale : MorphismProperty Scheme.{u}) :=
    HasRingHomProperty.instIsZariskiLocalAtTarget (P := @Etale)
  have := Stacks.Descent.isStableUnderFlatBaseChange_of_isStableUnderBaseChange
    (@Etale : MorphismProperty Scheme.{u})
  Stacks.Descent.isLocalAtTarget_fpqcPrecoverage _

/-- **Stacks Project, Tag 02LA.** Finite morphisms of schemes are local on the base for the fpqc
topology. -/
@[ega "II 6.3.10" "Locality on X"]
private theorem isFinite_isLocalAtTarget_fpqc :
    MorphismProperty.IsLocalAtTarget (@IsFinite : MorphismProperty Scheme.{u})
      Scheme.fpqcPrecoverage :=
  Stacks.Morphisms.isFinite_isLocalAtTarget_fpqc_of_isAffineHom
    Stacks.Descent.isAffineHom_isLocalAtTarget_fpqc.{u}

/-- **Stacks Project, Tag 07S0.** Every finite set of points on the source of a separated,
locally quasi-finite morphism to an affine scheme has a common affine open neighbourhood.

The locally quasi-finite hypothesis of the source is expressed by `LocallyOfFiniteType`
together with `LocallyQuasiFinite`, following the pointwise characterization of Tag 01TD. -/
private theorem exists_affineOpen_containing_finite_of_isAffine
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsSeparated f]
    [LocallyOfFiniteType f] [LocallyQuasiFinite f] [IsAffine Y]
    {s : Set X} (hs : s.Finite) :
    ∃ U : X.Opens, IsAffineOpen U ∧ s ⊆ U := by
  classical
  have : Finite s := hs.to_subtype
  choose V hV hxV _ using fun x : s =>
    exists_isAffineOpen_mem_and_subset (U := ⊤) (Set.mem_univ (x : X))
  let U : X.Opens := ⨆ x : s, V x
  have hsU : s ⊆ U := fun x hx => (le_iSup V ⟨x, hx⟩) (hxV ⟨x, hx⟩)
  let : CompactSpace U.toScheme := isCompact_iff_compactSpace.mp (by
    simpa [U] using isCompact_iUnion fun x => (hV x).isCompact)
  have : QuasiCompact (U.ι ≫ f) := (quasiCompact_iff_compactSpace _).mpr inferInstance
  have : IsQuasiAffineHom (U.ι ≫ f) := isQuasiAffineHom_of_locallyQuasiFinite (U.ι ≫ f)
  have : Scheme.IsQuasiAffine ((⊤ : U.toScheme.Opens) : Scheme) := by
    simpa using (isQuasiAffineHom_iff (U.ι ≫ f)).mp inferInstance (⊤ : Y.Opens)
      (isAffineOpen_top Y)
  let : U.toScheme.IsQuasiAffine := Scheme.IsQuasiAffine.of_isImmersion U.toScheme.topIso.inv
  obtain ⟨W, hW, hEW⟩ :=
    Stacks.AmpleCluster.exists_affineOpen_containing_finite_of_isQuasiAffine
      (X := U.toScheme) (hs.preimage fun a _ b _ hab => U.ι.isOpenEmbedding.injective hab)
  let : IsAffine W.toScheme := hW
  refine ⟨(W.ι ≫ U.ι).opensRange, isAffineOpen_opensRange _, fun x hx => ?_⟩
  exact Scheme.Hom.mem_opensRange.mpr ⟨⟨⟨x, hsU hx⟩,
    hEW (show U.ι (⟨x, hsU hx⟩ : U.toScheme) ∈ s from by simpa using hx)⟩, by rfl⟩

/-- **Stacks Project, Tag 0BL5.** Relative morphisms from a finite locally free scheme to a
separated, locally quasi-finite scheme form a representable functor. -/
private theorem relativeHom_isRepresentable {S Z X : Scheme.{u}} (f : Z ⟶ S) (g : X ⟶ S)
    [Stacks.Morphisms.IsFiniteLocallyFree f] [IsSeparated g] [LocallyOfFiniteType g]
    [LocallyQuasiFinite g] :
    ((Limits.prod.functor.obj (Over.mk f)).op ⋙ yoneda.obj (Over.mk g)).IsRepresentable := by
  refine Stacks.Morphisms.homFromFiniteLocallyFree_isRepresentable f g (fun s t ht hbase ↦ ?_)
  classical
  obtain ⟨_, ⟨W, hW, rfl⟩, hsW, -⟩ :=
    S.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ s) isOpen_univ
  let : IsAffine W := hW
  let V := g ⁻¹ᵁ W
  let q : t → V := fun x ↦ ⟨x.1, by
    show g.base x.1 ∈ W
    rw [hbase x.1 x.2]
    exact hsW⟩
  let : Fintype t := ht.fintype
  obtain ⟨Z', hZ', hsub⟩ :=
    exists_affineOpen_containing_finite_of_isAffine (g ∣_ W) (Set.finite_range q)
  exact ⟨V.ι ''ᵁ Z', hZ'.image_of_isOpenImmersion V.ι,
    fun x hx ↦ ⟨q ⟨x, hx⟩, hsub ⟨⟨x, hx⟩, rfl⟩, rfl⟩⟩

/-! ### The internal hom -/

/-- Near a point of the base, a finite étale scheme becomes a disjoint union of finitely many
copies of the base after base change to an étale neighbourhood of the point. -/
private theorem exists_etaleBaseChange_sigmaIso {X : Scheme.{u}} (U : Over X)
    [IsFinite U.hom] [Etale U.hom] (x : X) :
    ∃ (N : EtaleNeighborhood X x) (n : ℕ),
      Nonempty
        (Over.mk (Sigma.desc (fun _ : Fin n => 𝟙 N.scheme)) ≅
          (Over.pullback N.toBase).obj U) := by
  classical
  obtain ⟨T, g, hg, t, ht, ι, hι, e, he⟩ :=
    Stacks.Etale.exists_etale_pullback_iso_sigma U.hom x
  have : Etale g := hg
  have : Finite ι := hι
  let : Fintype ι := Fintype.ofFinite ι
  let r : (∐ fun _ : Fin (Fintype.card ι) => T) ≅ ∐ fun _ : ι => T :=
    Sigma.whiskerEquiv (Fintype.equivFin ι).symm fun _ => Iso.refl T
  have hsnd : e.inv ≫ pullback.snd U.hom g = Sigma.desc (fun _ : ι => 𝟙 T) := by
    rw [← he, Iso.inv_hom_id_assoc]
  refine ⟨{ scheme := T, point := t, toBase := g, map_point := ht },
    Fintype.card ι, ⟨Over.isoMk (r ≪≫ e.symm) ?_⟩⟩
  show (r.hom ≫ e.inv) ≫ pullback.snd U.hom g =
    Sigma.desc (fun _ : Fin (Fintype.card ι) => 𝟙 T)
  rw [Category.assoc, hsnd]
  apply Sigma.hom_ext
  intro i
  simp [r]

/-- A finite étale scheme over `X` becomes a disjoint union of finitely many copies of the base
over every member of an fppf covering of `X` by étale neighbourhoods of its points. -/
private theorem exists_fppfCover_etaleNeighborhoods {X : Scheme.{u}} (U : Over X)
    [IsFinite U.hom] [Etale U.hom] :
    ∃ (N : ∀ x : X, EtaleNeighborhood X x) (n : ∀ x : X, ℕ),
      (∀ x, Nonempty
        (Over.mk (Sigma.desc (fun _ : Fin (n x) => 𝟙 (N x).scheme)) ≅
          (Over.pullback (N x).toBase).obj U)) ∧
      Presieve.ofArrows (fun x => (N x).scheme) (fun x => (N x).toBase) ∈
        Scheme.fppfPrecoverage X := by
  classical
  choose N n hsigma using fun x : X => exists_etaleBaseChange_sigmaIso U x
  refine ⟨N, n, hsigma, ?_⟩
  rw [Scheme.fppfPrecoverage, Scheme.ofArrows_mem_precoverage_iff]
  refine ⟨?_, ?_⟩
  · intro x
    exact ⟨x, (N x).point, by simpa using (N x).map_point⟩
  · intro x
    exact ⟨inferInstance, inferInstance⟩

/-- **Stacks Project, Tag 0BL7.** The internal hom between two finite étale schemes over `X` is
represented by a finite étale scheme over `X`, compatibly with every base change: the
representing object is exhibited by an isomorphism of functors on the whole of `(Over X)ᵒᵖ`. -/
@[stacks 0BL7]
public theorem exists_finiteEtale_internalHom (X : Scheme.{u}) (U V : Over X)
    [IsFinite U.hom] [Etale U.hom] [IsFinite V.hom] [Etale V.hom] :
    ∃ W : Over X, IsFinite W.hom ∧ Etale W.hom ∧
      Nonempty
        (yoneda.obj W ≅
          (Limits.prod.functor.obj U).op ⋙ yoneda.obj V) := by
  let F : (Over X)ᵒᵖ ⥤ Type _ := (Limits.prod.functor.obj U).op ⋙ yoneda.obj V
  let : Flat U.hom := by infer_instance
  let : Flat V.hom := by infer_instance
  let : LocallyOfFinitePresentation U.hom := by infer_instance
  let : LocallyOfFinitePresentation V.hom := by infer_instance
  let : LocallyOfFiniteType V.hom := by infer_instance
  let : LocallyQuasiFinite V.hom := by infer_instance
  let : Stacks.Morphisms.IsFiniteLocallyFree U.hom :=
    (Stacks.Morphisms.isFiniteLocallyFree_iff_isFinite_flat_locallyOfFinitePresentation
      U.hom).2 ⟨inferInstance, inferInstance, inferInstance⟩
  let : IsSeparated V.hom := by infer_instance
  let : F.IsRepresentable := relativeHom_isRepresentable U.hom V.hom
  obtain ⟨N, nLocal, hsigmaLocal, hcoverFppf⟩ := exists_fppfCover_etaleNeighborhoods U
  have hcoverFpqc :
      Presieve.ofArrows (fun x => (N x).scheme) (fun x => (N x).toBase) ∈
        Scheme.fpqcPrecoverage X :=
    Scheme.fppfPrecoverage_le_fpqcPrecoverage X hcoverFppf
  have hlocal (x : X) :
      IsFinite ((Over.pullback (N x).toBase).obj F.reprX).hom ∧
        Etale ((Over.pullback (N x).toBase).obj F.reprX).hom := by
    let g := (N x).toBase
    let WN := (Over.pullback g).obj F.reprX
    let VT := (Over.pullback g).obj V
    let n := nLocal x
    obtain ⟨eU⟩ := hsigmaLocal x
    let P : Over (N x).scheme := ∏ᶜ fun _ : Fin n => VT
    let hrepr : yoneda.obj WN ≅ (Over.map g).op ⋙ F :=
      adjunctionYonedaIso (Over.mapPullbackAdj g) F.reprX ≪≫
        Functor.isoWhiskerLeft (Over.map g).op F.reprW
    have hbridge : (Over.map g).op ⋙ F ≅ yoneda.obj P := by
      show (Over.map g).op ⋙
          ((Limits.prod.functor.obj U).op ⋙ yoneda.obj V) ≅ yoneda.obj P
      exact splitInternalHomIso g U V eU.symm
    let eObj := yoneda.preimageIso (hrepr ≪≫ hbridge)
    have : IsIso eObj.hom.left := by
      show IsIso ((Over.forget (N x).scheme).map eObj.hom)
      infer_instance
    let : IsFinite VT.hom := by
      show IsFinite (pullback.snd V.hom g)
      infer_instance
    let : Etale VT.hom := by
      show Etale (pullback.snd V.hom g)
      infer_instance
    exact ⟨hom_of_iso_over (P := @IsFinite) eObj (pi_over_hom (P := @IsFinite) inferInstance n),
      hom_of_iso_over (P := @Etale) eObj (pi_over_hom (P := @Etale) inferInstance n)⟩
  have hfinite : IsFinite F.reprX.hom := by
    apply isFinite_isLocalAtTarget_fpqc.of_forall_pullbackSnd (f := F.reprX.hom) hcoverFpqc
    rintro _ _ _ ⟨x⟩
    exact (hlocal x).1
  have hetale : Etale F.reprX.hom := by
    apply etale_isLocalAtTarget_fpqc.of_forall_pullbackSnd (f := F.reprX.hom) hcoverFpqc
    rintro _ _ _ ⟨x⟩
    exact (hlocal x).2
  exact ⟨F.reprX, hfinite, hetale, ⟨F.reprW⟩⟩

end Stacks.FundamentalGroup

end

end
