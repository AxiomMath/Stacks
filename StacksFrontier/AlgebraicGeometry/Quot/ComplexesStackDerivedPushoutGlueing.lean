module

public import StacksFrontier.Homology.DerivedCategory.ModelComparison
public import StacksFrontier.AlgebraicGeometry.Quot.DerivedPullbackSectionFunctor
public import StacksFrontier.AlgebraicGeometry.Spaces.Pushouts.DerivedPushoutEssentialImage
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleDerivedPullbackDataCompIso

/-!
# The glueing input of Stacks 0DLK from the base statement of Stacks 0DL7

The proofs of Stacks 0DLK take Stacks 0DL7 as the hypothesis `h0DL7` of
`ComplexesSituation.isEquivalence_complexesFiberSquareComparison_of_pushouts` (in the namespace
`AlgebraicGeometry.Space`):
for a pushout square `k ≫ m = l ≫ n` of algebraic spaces with `k` a thickening and `l` affine,
pseudo-coherent `M ∈ D(𝒪_Q)` and `K' ∈ D(𝒪_{P'})` and `α : Ll^* M ≅ Lk^* K'` glue to some
`N ∈ D(𝒪_{Q'})`, in the language of the derived pullback pseudofunctor
`AlgebraicGeometry.Space.smallEtaleDerivedPullbackData`. The statement of Stacks 0DL7 on the base,
`AlgebraicGeometry.Space.DerivedPushoutEssentialImage`, is the same content for the chosen pushout
`pushout i f`, at arbitrary models of the four derived categories. This file derives the first
from the second (at the standard models).

## Main results

* `AlgebraicGeometry.Space.exists_glue_of_isPushout_of_derivedPushoutEssentialImage`: the
  hypothesis `h0DL7` from `AlgebraicGeometry.Space.DerivedPushoutEssentialImage`.
* `AlgebraicGeometry.Space.exists_glue_pushout_of_derivedPushoutEssentialImage`: the same for the
  chosen pushout, in terms of `AlgebraicGeometry.Space.smallEtaleDerivedModulePullback`.
* `StacksDraft.PushoutGlueing.exists_glue_of_heq` (over abstract categories): glueing for a square
  conjugated by auto-equivalences isomorphic to the identity gives glueing for the square.
* `StacksDraft.PushoutGlueing.gluesAlongSquare_of_comp` (for a coherent pullback datum): glueing
  along a square moves along any map out of its corner, here the comparison of an arbitrary
  pushout with the chosen one.
* `StacksDraft.DerivedModel.modelEquivSelfFunctorIso`: the comparison of a model of the derived
  category with itself is isomorphic to the identity.

## Implementation notes

At the standard models, `AlgebraicGeometry.Space.smallEtaleDerivedModulePullbackOfModels` is
`Lf^*` conjugated by the comparisons `StacksDraft.DerivedModel.modelEquiv` of the standard model
with itself, which are not the identity by definition. The conjugation is undone over abstract
categories (`StacksDraft.PushoutGlueing.exists_glue_of_conj`). The category structures of
`StacksDraft.PushoutGlueing.exists_glue_of_heq` are plain implicit arguments, so that they are
unified from the instantiated base statement: elaborated separately, the instance terms of the two
sides differ in their auxiliary proofs, and the kernel does not compare the compatibility equations
built on them within its budget.

## References

* [Stacks Project, Tag 0DL7](https://stacks.math.columbia.edu/tag/0DL7)
* [Stacks Project, Tag 0DLK](https://stacks.math.columbia.edu/tag/0DLK)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u


namespace StacksDraft.PushoutGlueing

section SelfEquivalence

variable {D : Type*} [Category* D] (e : D ≌ D) (ε : e.functor ≅ 𝟭 D)

/-- An auto-equivalence whose functor is isomorphic to the identity has its inverse isomorphic
to the identity, through the counit. -/
noncomputable def inverseIsoId : e.inverse ≅ 𝟭 D :=
  (Functor.rightUnitor e.inverse).symm ≪≫ Functor.isoWhiskerLeft e.inverse ε.symm ≪≫ e.counitIso

/-- The unit followed by `StacksDraft.PushoutGlueing.inverseIsoId`, `Z ⟶ e⁻¹ e Z ⟶ e Z`, is the
inverse of `ε` at `Z`. -/
@[reassoc (attr := simp)]
theorem unitIso_hom_app_inverseIsoId_hom_app (Z : D) :
    e.unitIso.hom.app Z ≫ (inverseIsoId e ε).hom.app (e.functor.obj Z) = ε.inv.app Z := by
  simp only [inverseIsoId, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Functor.rightUnitor_inv_app, Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app,
    Category.id_comp]
  have h := ε.inv.naturality (e.unitIso.hom.app Z)
  simp only [Functor.id_map, Functor.comp_obj, Functor.id_obj] at h
  rw [reassoc_of% h, Equivalence.functor_unitIso_comp, Category.comp_id]

/-- The inverse of `StacksDraft.PushoutGlueing.unitIso_hom_app_inverseIsoId_hom_app`. -/
@[reassoc (attr := simp)]
theorem inverseIsoId_inv_app_unitIso_inv_app (Z : D) :
    (inverseIsoId e ε).inv.app (e.functor.obj Z) ≫ e.unitIso.inv.app Z = ε.hom.app Z := by
  rw [← cancel_epi (ε.inv.app Z), Iso.inv_hom_id_app, ← unitIso_hom_app_inverseIsoId_hom_app e ε,
    Category.assoc, Iso.hom_inv_id_app_assoc, Iso.hom_inv_id_app]

end SelfEquivalence

section Conj

variable {A B : Type*} [Category* A] [Category* B] (eA : A ≌ A) (eB : B ≌ B)
  (εA : eA.functor ≅ 𝟭 A) (εB : eB.functor ≅ 𝟭 B) (L : A ⥤ B)

/-- A functor conjugated by two auto-equivalences isomorphic to the identity is isomorphic to
the functor. -/
noncomputable def selfConjIso : eA.inverse ⋙ L ⋙ eB.functor ≅ L :=
  Functor.isoWhiskerLeft (eA.inverse ⋙ L) εB ≪≫ Functor.isoWhiskerRight (inverseIsoId eA εA) L

/-- The components of `StacksDraft.PushoutGlueing.selfConjIso`. -/
@[simp]
theorem selfConjIso_hom_app (Z : A) : (selfConjIso eA eB εA εB L).hom.app Z =
    εB.hom.app (L.obj (eA.inverse.obj Z)) ≫ L.map ((inverseIsoId eA εA).hom.app Z) := by
  simp [selfConjIso]

/-- The components of the inverse of `StacksDraft.PushoutGlueing.selfConjIso`. -/
@[simp]
theorem selfConjIso_inv_app (Z : A) : (selfConjIso eA eB εA εB L).inv.app Z =
    L.map ((inverseIsoId eA εA).inv.app Z) ≫ εB.inv.app (L.obj (eA.inverse.obj Z)) := by
  simp [selfConjIso]

end Conj

section Glue

variable {DY' DY DX DX' : Type*} [Category* DY'] [Category* DY] [Category* DX] [Category* DX']
  (eY' : DY' ≌ DY') (eY : DY ≌ DY) (eX : DX ≌ DX) (eX' : DX' ≌ DX')
  (εY' : eY'.functor ≅ 𝟭 _) (εY : eY.functor ≅ 𝟭 _) (εX : eX.functor ≅ 𝟭 _)
  (εX' : eX'.functor ≅ 𝟭 _)
  (Lj : DY' ⥤ DY) (Lf : DY ⥤ DX) (Lf' : DY' ⥤ DX') (Li : DX' ⥤ DX)
  (τ : Lj ⋙ Lf ≅ Lf' ⋙ Li)

/-- The 2-cell of the conjugated square, built from `τ` and the units as at arbitrary models. -/
noncomputable abbrev selfConjSquareIso :
    (eY'.inverse ⋙ Lj ⋙ eY.functor) ⋙ (eY.inverse ⋙ Lf ⋙ eX.functor) ≅
      (eY'.inverse ⋙ Lf' ⋙ eX'.functor) ⋙ (eX'.inverse ⋙ Li ⋙ eX.functor) :=
  Functor.isoWhiskerLeft eY'.inverse (Functor.isoWhiskerRight
    (Functor.isoWhiskerLeft Lj (Functor.isoWhiskerRight eY.unitIso.symm Lf ≪≫
      Functor.leftUnitor Lf) ≪≫ τ ≪≫
      Functor.isoWhiskerLeft Lf' ((Functor.leftUnitor Li).symm ≪≫
        Functor.isoWhiskerRight eX'.unitIso Li)) eX.functor)

/-- The key identity: the conjugated 2-cell is `τ` read through `selfConjIso`. -/
theorem selfConjSquareIso_hom_app_eq (M' : DY') :
    Lf.map ((selfConjIso eY' eY εY' εY Lj).inv.app M') ≫
        (selfConjIso eY eX εY εX Lf).inv.app ((eY'.inverse ⋙ Lj ⋙ eY.functor).obj M') ≫
        (selfConjSquareIso eY' eY eX eX' Lj Lf Lf' Li τ).hom.app M' ≫
        (selfConjIso eX' eX εX' εX Li).hom.app ((eY'.inverse ⋙ Lf' ⋙ eX'.functor).obj M') =
      τ.hom.app M' ≫ Li.map ((selfConjIso eY' eX' εY' εX' Lf').inv.app M') := by
  set M'' := eY'.inverse.obj M'
  have hX := fun {Z₁ Z₂ : DX} (g : Z₁ ⟶ Z₂) => εX.hom.naturality g
  simp only [Functor.id_map] at hX
  have hτ := τ.hom.naturality ((inverseIsoId eY' εY').inv.app M')
  simp only [Functor.comp_map] at hτ
  simp only [selfConjIso_hom_app, selfConjIso_inv_app, Functor.comp_obj, Functor.isoWhiskerLeft_hom,
    Functor.isoWhiskerRight_hom, Iso.trans_hom, NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, Iso.symm_hom, Functor.leftUnitor_hom_app, Functor.leftUnitor_inv_app,
    Category.id_comp, Functor.map_comp, Category.assoc]
  have e1 := hX (Lf.map (eY.unitIso.inv.app (Lj.obj M'')) ≫ 𝟙 _ ≫ τ.hom.app M'' ≫
    Li.map (eX'.unitIso.hom.app (Lf'.obj M'')))
  simp only [Functor.map_comp, Category.assoc, Functor.id_obj] at e1
  have e2 : Lf.map (εY.inv.app (Lj.obj M'')) ≫
      Lf.map ((inverseIsoId eY εY).inv.app (eY.functor.obj (Lj.obj M''))) ≫
        Lf.map (eY.unitIso.inv.app (Lj.obj M'')) = 𝟙 _ := by
    rw [← Lf.map_comp, ← Lf.map_comp, inverseIsoId_inv_app_unitIso_inv_app, Iso.inv_hom_id_app,
      Lf.map_id]
  have e3 : Li.map (eX'.unitIso.hom.app (Lf'.obj M'')) ≫
      Li.map ((inverseIsoId eX' εX').hom.app (eX'.functor.obj (Lf'.obj M''))) =
        Li.map (εX'.inv.app (Lf'.obj M'')) := by
    rw [← Li.map_comp, unitIso_hom_app_inverseIsoId_hom_app]
  rw [reassoc_of% e1, Iso.inv_hom_id_app_assoc]
  rw [reassoc_of% e2, e3, reassoc_of% hτ]

include εY' εY εX εX' in
/-- **Glueing through conjugation by auto-equivalences isomorphic to the identity.** If every
triple `(M, K', α)` for the conjugated square is glued, so is every triple for the square itself
(for the same objects and predicates). The 2-cell of the square is `τ`. -/
theorem exists_glue_of_conj (PY : DY → Prop) (PX' : DX' → Prop)
    (H : ∀ (M : DY) (K' : DX'), PY M → PX' K' →
      ∀ α : (eY.inverse ⋙ Lf ⋙ eX.functor).obj M ≅ (eX'.inverse ⋙ Li ⋙ eX.functor).obj K',
        ∃ (M' : DY') (a : (eY'.inverse ⋙ Lj ⋙ eY.functor).obj M' ≅ M)
          (b : (eY'.inverse ⋙ Lf' ⋙ eX'.functor).obj M' ≅ K'),
          (selfConjSquareIso eY' eY eX eX' Lj Lf Lf' Li τ).hom.app M' ≫
              (eX'.inverse ⋙ Li ⋙ eX.functor).map b.hom =
            (eY.inverse ⋙ Lf ⋙ eX.functor).map a.hom ≫ α.hom)
    (M : DY) (K' : DX') (hM : PY M) (hK' : PX' K') (α : Lf.obj M ≅ Li.obj K') :
    ∃ (N : DY') (a : Lj.obj N ≅ M) (b : Lf'.obj N ≅ K'),
      τ.hom.app N ≫ Li.map b.hom = Lf.map a.hom ≫ α.hom := by
  obtain ⟨M', a, b, h⟩ := H M K' hM hK'
    ((selfConjIso eY eX εY εX Lf).app M ≪≫ α ≪≫ ((selfConjIso eX' eX εX' εX Li).app K').symm)
  refine ⟨M', ((selfConjIso eY' eY εY' εY Lj).app M').symm ≪≫ a,
    ((selfConjIso eY' eX' εY' εX' Lf').app M').symm ≪≫ b, ?_⟩
  have hb := (selfConjIso eX' eX εX' εX Li).hom.naturality b.hom
  have ha := (selfConjIso eY eX εY εX Lf).hom.naturality a.hom
  have key := selfConjSquareIso_hom_app_eq eY' eY eX eX' εY' εY εX εX' Lj Lf Lf' Li τ M'
  simp only [Iso.trans_hom, Iso.symm_hom, Iso.app_hom, Iso.app_inv, Functor.map_comp,
    Category.assoc] at h ⊢
  simp only [Functor.comp_map, Functor.comp_obj] at ha hb ⊢
  rw [← reassoc_of% key, ← hb, reassoc_of% h, reassoc_of% ha]
  simp

/-- The conjugated 2-cell for `τ = τ₁ ≪≫ eqToIso hG ≪≫ τ₃.symm`, bracketed as at arbitrary models
(`AlgebraicGeometry.Space.pushoutDerivedPullbackSquareIsoOfModels`). -/
noncomputable abbrev selfConjSquareIso₃ {G G' : DY' ⥤ DX} (τ₁ : Lj ⋙ Lf ≅ G) (hG : G = G')
    (τ₃ : Lf' ⋙ Li ≅ G') :
    (eY'.inverse ⋙ Lj ⋙ eY.functor) ⋙ (eY.inverse ⋙ Lf ⋙ eX.functor) ≅
      (eY'.inverse ⋙ Lf' ⋙ eX'.functor) ⋙ (eX'.inverse ⋙ Li ⋙ eX.functor) :=
  Functor.isoWhiskerLeft eY'.inverse (Functor.isoWhiskerRight
    (Functor.isoWhiskerLeft Lj (Functor.isoWhiskerRight eY.unitIso.symm Lf ≪≫
      Functor.leftUnitor Lf) ≪≫ τ₁ ≪≫ eqToIso hG ≪≫ τ₃.symm ≪≫
      Functor.isoWhiskerLeft Lf' ((Functor.leftUnitor Li).symm ≪≫
        Functor.isoWhiskerRight eX'.unitIso Li)) eX.functor)

/-- `StacksDraft.PushoutGlueing.selfConjSquareIso₃` is the conjugated 2-cell of the composite. -/
theorem selfConjSquareIso₃_eq {G G' : DY' ⥤ DX} (τ₁ : Lj ⋙ Lf ≅ G) (hG : G = G')
    (τ₃ : Lf' ⋙ Li ≅ G') :
    selfConjSquareIso₃ eY' eY eX eX' Lj Lf Lf' Li τ₁ hG τ₃ =
      selfConjSquareIso eY' eY eX eX' Lj Lf Lf' Li (τ₁ ≪≫ eqToIso hG ≪≫ τ₃.symm) := by
  simp only [selfConjSquareIso₃, selfConjSquareIso, Iso.trans_assoc]

end Glue

section GlueUnified

variable {DY' DY DX DX' : Type*} {_ : Category DY'} {_ : Category DY} {_ : Category DX}
  {_ : Category DX'}

/-- `StacksDraft.PushoutGlueing.exists_glue_of_conj` with the square `Tj, Tf, Tf', Ti, σ` taken
from the hypothesis `H` (so that the category structures are unified from it), equal to the
conjugated square, and the compatibility read componentwise for
`τ = τ₁ ≪≫ eqToIso hG ≪≫ τ₃.symm`. -/
theorem exists_glue_of_heq {Tj : DY' ⥤ DY} {Tf : DY ⥤ DX} {Tf' : DY' ⥤ DX'} {Ti : DX' ⥤ DX}
    {σ : Tj ⋙ Tf ≅ Tf' ⋙ Ti} {PY : DY → Prop} {PX' : DX' → Prop}
    (H : ∀ (M : DY) (K' : DX'), PY M → PX' K' → ∀ α : Tf.obj M ≅ Ti.obj K',
        ∃ (M' : DY') (a : Tj.obj M' ≅ M) (b : Tf'.obj M' ≅ K'),
          σ.hom.app M' ≫ Ti.map b.hom = Tf.map a.hom ≫ α.hom)
    (eY' : DY' ≌ DY') (eY : DY ≌ DY) (eX : DX ≌ DX) (eX' : DX' ≌ DX')
    (εY' : eY'.functor ≅ 𝟭 _) (εY : eY.functor ≅ 𝟭 _) (εX : eX.functor ≅ 𝟭 _)
    (εX' : eX'.functor ≅ 𝟭 _)
    (Lj : DY' ⥤ DY) (Lf : DY ⥤ DX) (Lf' : DY' ⥤ DX') (Li : DX' ⥤ DX)
    {G G' : DY' ⥤ DX} (τ₁ : Lj ⋙ Lf ≅ G) (hG : G = G') (τ₃ : Lf' ⋙ Li ≅ G')
    (hj : Tj = eY'.inverse ⋙ Lj ⋙ eY.functor) (hf : Tf = eY.inverse ⋙ Lf ⋙ eX.functor)
    (hf' : Tf' = eY'.inverse ⋙ Lf' ⋙ eX'.functor) (hi : Ti = eX'.inverse ⋙ Li ⋙ eX.functor)
    (hσ : HEq σ (selfConjSquareIso eY' eY eX eX' Lj Lf Lf' Li (τ₁ ≪≫ eqToIso hG ≪≫ τ₃.symm)))
    (M : DY) (K' : DX') (hM : PY M) (hK' : PX' K') (α : Lf.obj M ≅ Li.obj K') :
    ∃ (N : DY') (a : Lj.obj N ≅ M) (b : Lf'.obj N ≅ K'),
      Lf.map a.hom ≫ α.hom = τ₁.hom.app N ≫ eqToHom (congrArg (fun F => F.obj N) hG) ≫
        τ₃.inv.app N ≫ Li.map b.hom := by
  subst hj hf hf' hi
  obtain rfl := eq_of_heq hσ
  obtain ⟨N, a, b, h⟩ := exists_glue_of_conj eY' eY eX eX' εY' εY εX εX' Lj Lf Lf' Li
    (τ₁ ≪≫ eqToIso hG ≪≫ τ₃.symm) PY PX' H M K' hM hK' α
  exact ⟨N, a, b, by simpa [eqToHom_app] using h.symm⟩

end GlueUnified


section Transport

universe v₁ v₂ u₁ u₂

variable {A : Type u₁} [Category.{v₁} A] {D : A → Type u₂} [∀ a, Category.{v₂} (D a)]
  (P : PullbackData A D)

/-- The associativity of the composition comparisons of a coherent pullback datum, at an
object. -/
theorem compIso_hom_app_comp_map_compIso_hom_app (hP : P.IsCoherent) {a b c d : A} (f : a ⟶ b)
    (g : b ⟶ c) (p : c ⟶ d) (N : D d) :
    (P.compIso f (g ≫ p)).hom.app N ≫ (P.pull f).map ((P.compIso g p).hom.app N) =
      eqToHom (congrArg (fun x => (P.pull x).obj N) (Category.assoc f g p).symm) ≫
        (P.compIso (f ≫ g) p).hom.app N ≫ (P.compIso f g).hom.app ((P.pull p).obj N) := by
  have h := congrArg (fun e => e.hom.app N)
    (hP.triangle_comp (f := f) (g := g) (p := p) rfl rfl rfl (Category.assoc f g p))
  simp only [PullbackData.triangle_eq, Iso.trans_hom, eqToIso.hom, NatTrans.comp_app,
    eqToHom_refl, Category.id_comp, Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app,
    Functor.isoWhiskerRight_hom, Functor.whiskerRight_app, Functor.associator_hom_app,
    Category.comp_id, eqToHom_app] at h
  rw [← h]
  simp

/-- The composition comparisons along equal morphisms differ by the induced identification. -/
theorem compIso_inv_app_comp_eqToHom_comp_compIso_hom_app {a b c : A} {r r' : a ⟶ b}
    (h : r = r') (ψ : b ⟶ c) (N : D c) :
    (P.compIso r ψ).inv.app N ≫
        eqToHom (congrArg (fun x => (P.pull x).obj N) (congrArg (· ≫ ψ) h)) ≫
        (P.compIso r' ψ).hom.app N =
      eqToHom (congrArg (fun x => (P.pull x).obj ((P.pull ψ).obj N)) h) := by
  subst h
  simp

/-- **A triple glues along a commutative square.** For a commutative square `k ≫ m = l ≫ n`,
objects `M` over `b` and `K'` over `a'` and `α : l^* M ≅ k^* K'`: there are `N` over `b'` and
`n^* N ≅ M`, `m^* N ≅ K'` compatible with `α`. -/
def GluesAlongSquare {a a' b b' : A} (k : a ⟶ a') (l : a ⟶ b) (m : a' ⟶ b') (n : b ⟶ b')
    (w : k ≫ m = l ≫ n) (M : D b) (K' : D a') (α : (P.pull l).obj M ≅ (P.pull k).obj K') :
    Prop :=
  ∃ (N : D b') (eQ : (P.pull n).obj N ≅ M) (eP' : (P.pull m).obj N ≅ K'),
    (P.pull l).map eQ.hom ≫ α.hom =
      (P.compIso l n).inv.app N ≫
        eqToHom (congrArg (fun g => (P.pull g).obj N) w.symm) ≫
        (P.compIso k m).hom.app N ≫ (P.pull k).map eP'.hom

/-- **Glueing moves along a map out of the corner.** If `(M, K', α)` glues along the square
`k ≫ m₁ = l ≫ n₁` and `m₁ = m ≫ ψ`, `n₁ = n ≫ ψ`, it glues along `k ≫ m = l ≫ n`: pull the
glued object back along `ψ`. -/
theorem gluesAlongSquare_of_comp (hP : P.IsCoherent) {a a' b b' b₁ : A} (k : a ⟶ a')
    (l : a ⟶ b) (m : a' ⟶ b') (n : b ⟶ b') (w : k ≫ m = l ≫ n) (ψ : b' ⟶ b₁)
    {m₁ : a' ⟶ b₁} {n₁ : b ⟶ b₁} (hm : m ≫ ψ = m₁) (hn : n ≫ ψ = n₁) (w₁ : k ≫ m₁ = l ≫ n₁)
    (M : D b) (K' : D a') (α : (P.pull l).obj M ≅ (P.pull k).obj K')
    (h : GluesAlongSquare P k l m₁ n₁ w₁ M K' α) :
    GluesAlongSquare P k l m n w M K' α := by
  subst hm hn
  obtain ⟨N₀, eQ₀, eP₀, h⟩ := h
  refine ⟨(P.pull ψ).obj N₀, ((P.compIso n ψ).app N₀).symm ≪≫ eQ₀,
    ((P.compIso m ψ).app N₀).symm ≪≫ eP₀, ?_⟩
  have hl := compIso_hom_app_comp_map_compIso_hom_app P hP l n ψ N₀
  have hk := compIso_hom_app_comp_map_compIso_hom_app P hP k m ψ N₀
  have hl' : (P.pull l).map ((P.compIso n ψ).inv.app N₀) ≫ (P.compIso l (n ≫ ψ)).inv.app N₀ =
      (P.compIso l n).inv.app ((P.pull ψ).obj N₀) ≫ (P.compIso (l ≫ n) ψ).inv.app N₀ ≫
        eqToHom (congrArg (fun x => (P.pull x).obj N₀) (Category.assoc l n ψ)) := by
    rw [← cancel_mono ((P.compIso l (n ≫ ψ)).hom.app N₀ ≫
      (P.pull l).map ((P.compIso n ψ).hom.app N₀))]
    conv_rhs => rw [hl]
    simp [← Functor.map_comp]
  have hk' : (P.compIso k (m ≫ ψ)).hom.app N₀ =
      eqToHom (congrArg (fun x => (P.pull x).obj N₀) (Category.assoc k m ψ).symm) ≫
        (P.compIso (k ≫ m) ψ).hom.app N₀ ≫ (P.compIso k m).hom.app ((P.pull ψ).obj N₀) ≫
        (P.pull k).map ((P.compIso m ψ).inv.app N₀) := by
    rw [← reassoc_of% hk]
    simp [← Functor.map_comp]
  simp only [Iso.trans_hom, Iso.symm_hom, Iso.app_inv, Functor.map_comp, Category.assoc]
  rw [h, reassoc_of% hl', hk']
  simp only [Category.assoc, eqToHom_trans_assoc]
  rw [reassoc_of% (compIso_inv_app_comp_eqToHom_comp_compIso_hom_app P w.symm ψ N₀)]

end Transport

end StacksDraft.PushoutGlueing

namespace StacksDraft.DerivedModel

/-- The comparison of a model of the derived category with itself is isomorphic to the
identity. -/
noncomputable def modelEquivSelfFunctorIso {C : Type*} [Category* C] [Abelian C]
    (h : HasDerivedCategory C) : (modelEquiv h h).functor ≅ 𝟭 _ := by
  letI := h
  exact Localization.liftNatIso (DerivedCategory.Qh) (HomotopyCategory.subcategoryAcyclic C).trW
    DerivedCategory.Qh DerivedCategory.Qh _ _ (Iso.refl _)

end StacksDraft.DerivedModel

namespace AlgebraicGeometry.Space

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The standard model of `D(𝒪_X)`, for the small étale ringed topos of `X`. -/
noncomputable abbrev smallEtaleStdModel (X : AlgebraicSpaces B S hS) :
    HasDerivedCategory.{u + 1} (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)) :=
  HasDerivedCategory.standard _

/-- The comparison of the standard model of `D(𝒪_X)` with itself. -/
noncomputable abbrev smallEtaleSelfModelEquiv (X : AlgebraicSpaces B S hS) :=
  StacksDraft.DerivedModel.modelEquiv (smallEtaleStdModel B S hS X) (smallEtaleStdModel B S hS X)

/-- `AlgebraicGeometry.Space.smallEtaleSelfModelEquiv` is isomorphic to the identity. -/
noncomputable abbrev smallEtaleSelfModelEquivIso (X : AlgebraicSpaces B S hS) :
    (smallEtaleSelfModelEquiv B S hS X).functor ≅ 𝟭 _ :=
  StacksDraft.DerivedModel.modelEquivSelfFunctorIso _

/-- At the standard models, the 2-cell `Lf^* ∘ Lj^* ≅ Li^* ∘ L(f')^*` of the pushout square is the
conjugated 2-cell of Stacks 0D6D twice, through
`AlgebraicGeometry.Space.smallEtaleSelfModelEquiv`. -/
theorem pushoutDerivedPullbackSquareIsoOfModels_standard_eq {X X' Y : AlgebraicSpaces B S hS}
    (i : X ⟶ X') (f : X ⟶ Y) [HasPushout i f] :
    pushoutDerivedPullbackSquareIsoOfModels i f (pushout.inl i f) (pushout.inr i f)
      pushout.condition (smallEtaleStdModel B S hS _) (smallEtaleStdModel B S hS _)
      (smallEtaleStdModel B S hS _) (smallEtaleStdModel B S hS _) =
    StacksDraft.PushoutGlueing.selfConjSquareIso
    (smallEtaleSelfModelEquiv B S hS (pushout i f)) (smallEtaleSelfModelEquiv B S hS Y)
    (smallEtaleSelfModelEquiv B S hS X) (smallEtaleSelfModelEquiv B S hS X')
    (smallEtaleDerivedModulePullback B S hS (pushout.inr i f))
    (smallEtaleDerivedModulePullback B S hS f)
    (smallEtaleDerivedModulePullback B S hS (pushout.inl i f))
    (smallEtaleDerivedModulePullback B S hS i)
    (smallEtaleDerivedModulePullbackCompIso B S hS f (pushout.inr i f) ≪≫
        eqToIso (congrArg (fun g => smallEtaleDerivedModulePullback B S hS g)
          pushout.condition.symm) ≪≫
        (smallEtaleDerivedModulePullbackCompIso B S hS i (pushout.inl i f)).symm) :=
  StacksDraft.PushoutGlueing.selfConjSquareIso₃_eq _ _ _ _ _ _ _ _ _ _ _

/-- **Stacks 0DL7 at the standard models, for the chosen pushout.** Given the base statement
`AlgebraicGeometry.Space.DerivedPushoutEssentialImage`, every pseudo-coherent triple `(M, K', α)`
with `α : Lf^* M ≅ Li^* K'` glues to some `N` on `pushout i f`, compatibly with `α` through Stacks
0D6D (`AlgebraicGeometry.Space.smallEtaleDerivedModulePullbackCompIso`). -/
theorem exists_glue_pushout_of_derivedPushoutEssentialImage
    (h : DerivedPushoutEssentialImage.{u + 1, u + 1, u + 1, u + 1, u} B S hS)
    {X X' Y : AlgebraicSpaces B S hS} (i : X ⟶ X') (f : X ⟶ Y)
    (hi : IsThickeningHom B S hS i) (hf : IsAffineHom B S hS f.hom) [HasPushout i f]
    (M : derivedModules B S hS Y) (K' : derivedModules B S hS X')
    (hM : IsPseudoCoherentObject M) (hK' : IsPseudoCoherentObject K')
    (α : (smallEtaleDerivedModulePullback B S hS f).obj M ≅
      (smallEtaleDerivedModulePullback B S hS i).obj K') :
    ∃ (N : derivedModules B S hS (pushout i f))
      (a : (smallEtaleDerivedModulePullback B S hS (pushout.inr i f)).obj N ≅ M)
      (b : (smallEtaleDerivedModulePullback B S hS (pushout.inl i f)).obj N ≅ K'),
      (smallEtaleDerivedModulePullback B S hS f).map a.hom ≫ α.hom =
        (smallEtaleDerivedModulePullbackCompIso B S hS f (pushout.inr i f)).hom.app N ≫
          eqToHom (congrArg (fun F => F.obj N)
            (congrArg (fun g => smallEtaleDerivedModulePullback B S hS g) pushout.condition.symm)) ≫
          (smallEtaleDerivedModulePullbackCompIso B S hS i (pushout.inl i f)).inv.app N ≫
          (smallEtaleDerivedModulePullback B S hS i).map b.hom :=
  StacksDraft.PushoutGlueing.exists_glue_of_heq
    (h i f hi hf (smallEtaleStdModel B S hS _) (smallEtaleStdModel B S hS _)
      (smallEtaleStdModel B S hS _) (smallEtaleStdModel B S hS _))
    (smallEtaleSelfModelEquiv B S hS (pushout i f)) (smallEtaleSelfModelEquiv B S hS Y)
    (smallEtaleSelfModelEquiv B S hS X) (smallEtaleSelfModelEquiv B S hS X')
    (smallEtaleSelfModelEquivIso B S hS _) (smallEtaleSelfModelEquivIso B S hS _)
    (smallEtaleSelfModelEquivIso B S hS _) (smallEtaleSelfModelEquivIso B S hS _)
    (smallEtaleDerivedModulePullback B S hS (pushout.inr i f))
    (smallEtaleDerivedModulePullback B S hS f)
    (smallEtaleDerivedModulePullback B S hS (pushout.inl i f))
    (smallEtaleDerivedModulePullback B S hS i)
    (smallEtaleDerivedModulePullbackCompIso B S hS f (pushout.inr i f))
    (congrArg (fun g => smallEtaleDerivedModulePullback B S hS g) pushout.condition.symm)
    (smallEtaleDerivedModulePullbackCompIso B S hS i (pushout.inl i f))
    rfl rfl rfl rfl (heq_of_eq (pushoutDerivedPullbackSquareIsoOfModels_standard_eq B S hS i f))
    M K' hM hK' α

/-- **The hypothesis `h0DL7` of the Stacks 0DLK theorems from the base statement of Stacks 0DL7.**
For any pushout square `k ≫ m = l ≫ n` of algebraic spaces with `k` a thickening and `l` affine,
pseudo-coherent `M` and `K'` and `α : Ll^* M ≅ Lk^* K'` glue to some `N` with `n^* N ≅ M` and
`m^* N ≅ K'` compatible with `α`, in the language of
`AlgebraicGeometry.Space.smallEtaleDerivedPullbackData`. This is exactly the binder `h0DL7` of
`ComplexesSituation.isEquivalence_complexesFiberSquareComparison_of_pushouts`. -/
theorem exists_glue_of_isPushout_of_derivedPushoutEssentialImage
    (h : DerivedPushoutEssentialImage.{u + 1, u + 1, u + 1, u + 1, u} B S hS) :
    ∀ {P P' Q Q' : AlgebraicSpaces B S hS} (k : P ⟶ P') (l : P ⟶ Q) (m : P' ⟶ Q')
      (n : Q ⟶ Q') (hsq : IsPushout k l m n),
      IsThickeningHom B S hS k → IsAffineHom B S hS l.hom →
      ∀ (M : derivedModules B S hS Q) (K' : derivedModules B S hS P'),
        IsPseudoCoherentObject M → IsPseudoCoherentObject K' →
        ∀ α : ((smallEtaleDerivedPullbackData B S hS).pull l).obj M ≅
            ((smallEtaleDerivedPullbackData B S hS).pull k).obj K',
          ∃ (N : derivedModules B S hS Q')
            (eQ : ((smallEtaleDerivedPullbackData B S hS).pull n).obj N ≅ M)
            (eP' : ((smallEtaleDerivedPullbackData B S hS).pull m).obj N ≅ K'),
            ((smallEtaleDerivedPullbackData B S hS).pull l).map eQ.hom ≫ α.hom =
              ((smallEtaleDerivedPullbackData B S hS).compIso l n).inv.app N ≫
                eqToHom (congrArg
                  (fun g => ((smallEtaleDerivedPullbackData B S hS).pull g).obj N)
                  hsq.w.symm) ≫
                ((smallEtaleDerivedPullbackData B S hS).compIso k m).hom.app N ≫
                ((smallEtaleDerivedPullbackData B S hS).pull k).map eP'.hom := by
  intro P P' Q Q' k l m n hsq hk hl M K' hM hK' α
  have : HasPushout k l := hsq.hasPushout
  refine StacksDraft.PushoutGlueing.gluesAlongSquare_of_comp _
    (smallEtaleDerivedPullbackData_isCoherent B S hS) k l m n hsq.w hsq.isoPushout.hom
    hsq.inl_isoPushout_hom hsq.inr_isoPushout_hom pushout.condition M K' α ?_
  obtain ⟨N, a, b, hab⟩ :=
    exists_glue_pushout_of_derivedPushoutEssentialImage B S hS h k l hk hl M K' hM hK' α
  unfold StacksDraft.PushoutGlueing.GluesAlongSquare
  refine ⟨N, a, b, ?_⟩
  rw [smallEtaleDerivedPullbackData_compIso_eq, smallEtaleDerivedPullbackData_compIso_eq]
  exact hab

end AlgebraicGeometry.Space

end
