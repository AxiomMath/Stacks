module

public import StacksFrontier.AlgebraicGeometry.ProEtale.IndZariski.ComponentRestriction
public import StacksFrontier.AlgebraicGeometry.ProEtale.WLocal.StratificationColimit
public import StacksFrontier.AlgebraicGeometry.ProEtale.WLocal.StratificationStrataPoints
public import StacksFrontier.AlgebraicGeometry.ProEtale.IndZariski.Basic
public import StacksFrontier.AlgebraicGeometry.ProEtale.IndZariski.Localization
public import StacksFrontier.RingTheory.Flat.DirectLimit
public import Mathlib.RingTheory.Flat.Localization
public import Mathlib.RingTheory.RingHom.FaithfullyFlat
public import Mathlib.CategoryTheory.ObjectProperty.FiniteProducts
public import Mathlib.CategoryTheory.Limits.Shapes.Products
public import Mathlib.RingTheory.Finiteness.FinitePresentationLocal
public import Mathlib.RingTheory.Localization.Away.AdjoinRoot
public import Mathlib.Algebra.Category.CommAlgCat.FiniteType
public import Mathlib.Algebra.Category.Ring.FinitePresentation
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.ProEtale.WLocal.StratumIdempotent
public import StacksFrontier.AlgebraicGeometry.ProEtale.IndZariski.FilteredColimit

/-!
# The stratification colimit is ind-Zariski and faithfully flat

For a commutative ring `A`, the canonical map from `A` to the colimit `A_w` of its finite
vanishing-stratification rings is ind-Zariski and faithfully flat.

## Main results

* `AlgebraicGeometry.ProEtale.stratificationColimit_isIndZariski` states that `A → A_w` is
  ind-Zariski.
* `AlgebraicGeometry.ProEtale.stratificationColimit_faithfullyFlat` states that `A → A_w` is
  faithfully flat.
* `AlgebraicGeometry.ProEtale.stratificationColimit_isIndZariski_and_faithfullyFlat` combines
  the two into the single assertion that `A → A_w` is ind-Zariski and faithfully flat.

## Implementation notes

The two independent properties of the canonical map are proved separately, then conjoined.
Ind-Zariskiness is obtained by exhibiting `A_w` as a filtered colimit of the finite stages,
each of which is a finite product of localizations and hence itself a filtered colimit of local
isomorphisms; idempotence of the ind-completion then collapses the two layers. Faithful flatness
is the general statement that a directed colimit of faithfully flat algebras is faithfully flat,
applied to the finite stages.

## References

* [Stacks Project, Tag 0975](https://stacks.math.columbia.edu/tag/0975)
-/

@[expose] public noncomputable section

universe u

namespace AlgebraicGeometry.ProEtale

open CategoryTheory CategoryTheory.Limits

variable {A : Type u} [CommRing A]

private theorem stratificationRing_flat (E : Finset A) :
    Module.Flat A (stratificationRing E) := by
  classical
  let idx := {E' : Finset A // E' ⊆ E}
  let : Fintype idx := stratumIndexFintype E
  let : ∀ i : idx, Module.Flat A
      (localizationRing (stratumIdeal E i) (stratumOpenElement i.val)) :=
    fun i => IsLocalization.flat _
      (localizationSubmonoid (stratumIdeal E i) (stratumOpenElement i.val))
  let S : idx → Type u := fun i =>
    localizationRing (stratumIdeal E i) (stratumOpenElement i.val)
  let ePi : (Π₀ i, S i) ≃ₗ[A] stratificationRing E :=
    DFinsupp.linearEquivFunOnFintype
  exact Module.Flat.of_linearEquiv ePi.symm

private theorem stratificationAlgebraMap_eq_algebraMap (E : Finset A) :
    stratificationAlgebraMap E = algebraMap A (stratificationRing E) := by
  ext i a
  rfl

private theorem stratificationAlgebraMap_faithfullyFlat (E : Finset A) :
    (stratificationAlgebraMap E).FaithfullyFlat := by
  classical
  rw [RingHom.FaithfullyFlat.iff_flat_and_comap_surjective]
  refine ⟨?_, ?_⟩
  · rw [stratificationAlgebraMap_eq_algebraMap (A := A) E, RingHom.flat_algebraMap_iff]
    exact stratificationRing_flat E
  · intro p
    let i := finiteStratumIndex E p
    obtain ⟨q, hq⟩ : p ∈ Set.range (PrimeSpectrum.comap
        (algebraMap A (localizationRing (stratumIdeal E i)
          (stratumOpenElement i.val)))) := by
      rw [localization_comap_range]
      exact ⟨p, finiteStratumIndex_mem E p, specializes_refl p⟩
    refine ⟨q.comap (Pi.evalRingHom _ i), ?_⟩
    have hcomp : (Pi.evalRingHom _ i).comp (stratificationAlgebraMap E) =
        algebraMap A (localizationRing (stratumIdeal E i)
          (stratumOpenElement i.val)) := by
      ext a
      rfl
    change PrimeSpectrum.comap ((Pi.evalRingHom _ i).comp
      (stratificationAlgebraMap E)) q = p
    rw [hcomp]
    exact hq

private theorem stratificationColimit_algebraMap_eq_arbitrary
  [Nonempty (Finset A)] [IsDirectedOrder (Finset A)] :
    (Ring.DirectLimit.of (fun E : Finset A => stratificationRing E)
      (fun E₁ E₂ h => stratificationRingMap E₁ E₂ h)
      (Classical.arbitrary (Finset A))).comp
      (algebraMap A (stratificationRing (Classical.arbitrary (Finset A)))) =
      stratificationColimitAlgebraMap (A := A) := by
  rw [← stratificationColimitMap_comp_algebraMap (E := Classical.arbitrary (Finset A)),
    ← stratificationAlgebraMap_eq_algebraMap (A := A)]
  rfl

/-- The transition maps between finite stages commute with the structure maps from `A`. -/
private theorem stratificationRingMap_comp_algebraMap_eq (E₁ E₂ : Finset A) (h : E₁ ⊆ E₂) :
    (stratificationRingMap E₁ E₂ h).comp (algebraMap A (stratificationRing E₁)) =
      algebraMap A (stratificationRing E₂) := by
  rw [← stratificationAlgebraMap_eq_algebraMap (A := A) E₁,
    ← stratificationAlgebraMap_eq_algebraMap (A := A) E₂]
  exact stratificationRingMap_comp_algebraMap E₁ E₂ h

private def stratificationAlgHom (E₁ E₂ : Finset A) (h : E₁ ⊆ E₂) :
    stratificationRing E₁ →ₐ[A] stratificationRing E₂ :=
  { toRingHom := stratificationRingMap E₁ E₂ h
    commutes' := DFunLike.congr_fun (stratificationRingMap_comp_algebraMap_eq E₁ E₂ h) }

private noncomputable abbrev stratificationDiagram : Finset A ⥤ CommAlgCat A where
  obj E := CommAlgCat.of A (stratificationRing E)
  map {E₁ E₂} f := CommAlgCat.ofHom (stratificationAlgHom E₁ E₂ f.le)
  map_id E := CommAlgCat.hom_ext (AlgHom.ext fun x =>
    DFunLike.congr_fun (stratificationRingMap_id E) x)
  map_comp {E₁ E₂ E₃} f g := CommAlgCat.hom_ext (AlgHom.ext fun x =>
    (DFunLike.congr_fun (stratificationRingMap_comp E₁ E₂ E₃ f.le g.le) x).symm)

private noncomputable abbrev stratificationColimitAlgHom (E : Finset A) :
    stratificationRing E →ₐ[A] stratificationColimitRing (A := A) :=
  { toRingHom := stratificationColimitMap (A := A) E
    commutes' := fun a => by
      change stratificationColimitMap (A := A) E
        (algebraMap A (stratificationRing E) a) =
        algebraMap A (stratificationColimitRing (A := A)) a
      rw [← stratificationAlgebraMap_eq_algebraMap (A := A) E]
      exact DFunLike.congr_fun (stratificationColimitMap_comp_algebraMap E) a }

private theorem stratificationColimitMap_comp_ringMap (E₁ E₂ : Finset A)
    (h : E₁ ⊆ E₂) :
    (stratificationColimitMap (A := A) E₂).comp (stratificationRingMap E₁ E₂ h) =
      stratificationColimitMap (A := A) E₁ := by
  ext x
  exact Ring.DirectLimit.of_f
    (G := fun E : Finset A => stratificationRing E)
    (f := fun E₁ E₂ (h : E₁ ≤ E₂) => stratificationRingMap E₁ E₂ h)
    h x

private noncomputable abbrev stratificationColimitCocone :
    CategoryTheory.Limits.Cocone (stratificationDiagram (A := A)) where
  pt := CommAlgCat.of A (stratificationColimitRing (A := A))
  ι.app E := CommAlgCat.ofHom (stratificationColimitAlgHom (A := A) E)
  ι.naturality E₁ E₂ f := by
    change CommAlgCat.ofHom (stratificationAlgHom (A := A) E₁ E₂ f.le) ≫
        CommAlgCat.ofHom (stratificationColimitAlgHom (A := A) E₂) =
      CommAlgCat.ofHom (stratificationColimitAlgHom (A := A) E₁)
    exact CommAlgCat.hom_ext (AlgHom.ext fun x =>
      DFunLike.congr_fun
        (stratificationColimitMap_comp_ringMap (A := A) E₁ E₂ f.le) x)

private def stratificationColimitCocone_isColimit :
    CategoryTheory.Limits.IsColimit (stratificationColimitCocone (A := A)) := by
  classical
  let G : Finset A → Type u := fun E => stratificationRing E
  let f : ∀ E₁ E₂, E₁ ≤ E₂ → G E₁ → G E₂ :=
    fun E₁ E₂ h => stratificationRingMap E₁ E₂ h
  refine IsColimit.ofExistsUnique fun t => ?_
  have hcompat (E₁ E₂ : Finset A) (h : E₁ ≤ E₂) (x : G E₁) :
      (t.ι.app E₂).hom (f E₁ E₂ h x) = (t.ι.app E₁).hom x :=
    AlgHom.congr_fun (congrArg CommAlgCat.Hom.hom (t.w (homOfLE h))) x
  let g : ∀ E : Finset A, G E →+* (t.pt : Type u) :=
    fun E => (t.ι.app E).hom.toRingHom
  let desc : Ring.DirectLimit G f →ₐ[A] t.pt := {
    toRingHom := Ring.DirectLimit.lift G f t.pt g hcompat
    commutes' := fun a => by
      change Ring.DirectLimit.lift G f t.pt g hcompat
        (Ring.DirectLimit.of G f ∅ (stratificationAlgebraMap ∅ a)) = _
      rw [Ring.DirectLimit.lift_of, stratificationAlgebraMap_eq_algebraMap (A := A) ∅]
      exact (t.ι.app ∅).hom.commutes a }
  refine ⟨CommAlgCat.ofHom desc, ?_, ?_⟩
  · intro E
    apply CommAlgCat.hom_ext
    ext x
    change Ring.DirectLimit.lift G f t.pt g hcompat
      (Ring.DirectLimit.of G f E x) = (t.ι.app E).hom x
    rw [Ring.DirectLimit.lift_of]
    rfl
  · intro m hm
    ext x
    obtain ⟨E, y, rfl⟩ := Ring.DirectLimit.exists_of x
    change m.hom (Ring.DirectLimit.of G f E y) =
      Ring.DirectLimit.lift G f t.pt g hcompat (Ring.DirectLimit.of G f E y)
    rw [Ring.DirectLimit.lift_of]
    exact AlgHom.congr_fun (congrArg CommAlgCat.Hom.hom (hm E)) y

private instance localIso_closedUnderIsomorphisms :
    ObjectProperty.IsClosedUnderIsomorphisms
      (fun C : CommAlgCat.{u} A => Algebra.IsLocalIso A C) where
  of_iso {X Y} e h := by
    let : Algebra.IsLocalIso A X := h
    exact Algebra.IsLocalIso.of_algEquiv (CommAlgCat.algEquivOfIso e)

private noncomputable def commAlgCatPiIso {ι : Type u} [Fintype ι]
    (S : ι → Type u) [∀ i, CommRing (S i)] [∀ i, Algebra A (S i)] :
    (∏ᶜ fun i : ι => CommAlgCat.of A (S i)) ≅ CommAlgCat.of A (∀ i, S i) := by
  let D : Discrete ι ⥤ CommAlgCat.{u} A :=
    Discrete.functor fun i => CommAlgCat.of A (S i)
  let c : Cone D := {
    pt := CommAlgCat.of A (∀ i, S i)
    π := Discrete.natTrans fun i => CommAlgCat.ofHom (Pi.evalAlgHom A S i.as)
  }
  have hc : IsLimit c := {
    lift := fun s => CommAlgCat.ofHom
      (AlgHom.pi fun i => (s.π.app (Discrete.mk i)).hom)
    fac := fun _ _ => CommAlgCat.hom_ext (AlgHom.ext fun _ => rfl)
    uniq := fun _ _ hm => CommAlgCat.hom_ext (AlgHom.ext fun x => funext fun i =>
      AlgHom.congr_fun (congrArg CommAlgCat.Hom.hom (hm (Discrete.mk i))) x)
  }
  exact IsLimit.conePointUniqueUpToIso (productIsProduct' D) hc

private instance localIso_isClosedUnderFiniteProducts :
    ObjectProperty.IsClosedUnderFiniteProducts
      (fun C : CommAlgCat.{u} A => Algebra.IsLocalIso A C) := by
  apply ObjectProperty.IsClosedUnderFiniteProducts.of_isClosedUnderLimitsOfShape
  intro J hJ
  refine ⟨fun X ⟨p⟩ => ?_⟩
  let P : ObjectProperty (CommAlgCat.{u} A) := fun C => Algebra.IsLocalIso A C
  let : Fintype J := Fintype.ofFinite J
  let e : X ≅ CommAlgCat.of A (∀ j : J, (p.diag.obj (Discrete.mk j) : Type u)) :=
    p.isLimit.conePointUniqueUpToIso (limit.isLimit p.diag) ≪≫
      (Pi.isoLimit _).symm ≪≫
      commAlgCatPiIso (A := A) (fun j : J => p.diag.obj (Discrete.mk j))
  let : ∀ j : J, Algebra.IsLocalIso A (p.diag.obj (Discrete.mk j)) :=
    fun j => p.prop_diag_obj (Discrete.mk j)
  exact P.prop_of_iso e.symm
    (Algebra.IsLocalIso.pi_of_finite A fun j : J => (p.diag.obj (Discrete.mk j) : Type u))

private theorem localIso_prod_of_localIso (B C : Type u) [CommRing B] [CommRing C]
    [Algebra A B] [Algebra A C] (hB : Algebra.IsLocalIso A B)
    (hC : Algebra.IsLocalIso A C) : Algebra.IsLocalIso A (B × C) := by
  classical
  let S : Bool → Type u := fun b => match b with | false => B | true => C
  let : ∀ b : Bool, CommRing (S b) := fun b => by cases b <;> infer_instance
  let : ∀ b : Bool, Algebra A (S b) := fun b => by cases b <;> infer_instance
  let : ∀ b : Bool, Algebra.IsLocalIso A (S b) := fun b => by
    cases b
    · exact hB
    · exact hC
  let : Algebra.IsLocalIso A (∀ b : Bool, S b) := Algebra.IsLocalIso.pi_of_finite A S
  let e : (∀ b : Bool, S b) ≃ₐ[A] (B × C) := {
    toFun := fun f => (f false, f true)
    invFun := fun p b => match b with | false => p.1 | true => p.2
    left_inv := fun f => funext fun b => by cases b <;> rfl
    right_inv := fun _ => rfl
    map_mul' := fun _ _ => rfl
    map_add' := fun _ _ => rfl
    commutes' := fun a => by apply Prod.ext <;> simp [S] }
  exact Algebra.IsLocalIso.of_algEquiv e

private noncomputable def commAlgProductFunctor :
    CommAlgCat.{u} A × CommAlgCat.{u} A ⥤ CommAlgCat.{u} A where
  obj X := CommAlgCat.of A (X.1 × X.2)
  map f := CommAlgCat.ofHom {
    toRingHom := f.1.hom.toRingHom.prodMap f.2.hom.toRingHom
    commutes' := fun a => Prod.ext (f.1.hom.commutes a) (f.2.hom.commutes a) }
  map_id _ := CommAlgCat.hom_ext (AlgHom.ext fun _ => rfl)
  map_comp _ _ := CommAlgCat.hom_ext (AlgHom.ext fun _ => rfl)

private noncomputable def productCocone {I J : Type u} [Category.{u} I]
    [Category.{u} J] {C D : Type (u + 1)} [Category.{u} C] [Category.{u} D]
    {F : I ⥤ C} {G : J ⥤ D} (cF : Cocone F) (cG : Cocone G) :
    Cocone (F.prod G) where
  pt := (cF.pt, cG.pt)
  ι := {
    app := fun k => (cF.ι.app k.1, cG.ι.app k.2)
    naturality := by
      rintro ⟨i, j⟩ ⟨i', j'⟩ ⟨f, g⟩
      exact Prod.ext (cF.ι.naturality f) (cG.ι.naturality g) }

private noncomputable def productCocone_isColimit {I J : Type u}
    [Category.{u} I] [Category.{u} J] [IsFiltered I] [IsFiltered J]
    {C D : Type (u + 1)} [Category.{u} C] [Category.{u} D]
    {F : I ⥤ C} {G : J ⥤ D} (cF : Cocone F) (cG : Cocone G)
    (hF : IsColimit cF) (hG : IsColimit cG) :
    IsColimit (productCocone cF cG) := by
  have hF' : IsColimit (cF.whisker (CategoryTheory.Prod.fst I J)) :=
    (Functor.Final.isColimitWhiskerEquiv (CategoryTheory.Prod.fst I J) cF).symm hF
  have hG' : IsColimit (cG.whisker (CategoryTheory.Prod.snd I J)) :=
    (Functor.Final.isColimitWhiskerEquiv (CategoryTheory.Prod.snd I J) cG).symm hG
  exact {
    desc := fun s => (hF'.desc ((CategoryTheory.Prod.fst _ _).mapCocone s),
      hG'.desc ((CategoryTheory.Prod.snd _ _).mapCocone s))
    fac := fun s k => Prod.ext
      (hF'.fac ((CategoryTheory.Prod.fst _ _).mapCocone s) k)
      (hG'.fac ((CategoryTheory.Prod.snd _ _).mapCocone s) k)
    uniq := fun s m hm => Prod.ext
      (hF'.uniq ((CategoryTheory.Prod.fst _ _).mapCocone s) m.1 fun k =>
        congrArg Prod.fst (hm k))
      (hG'.uniq ((CategoryTheory.Prod.snd _ _).mapCocone s) m.2 fun k =>
        congrArg Prod.snd (hm k)) }

private theorem localIso_ind_prod (X Y : Type u) [CommRing X] [CommRing Y]
    [Algebra A X] [Algebra A Y]
    (hX : ObjectProperty.ind.{u}
      (fun Z : CommAlgCat.{u} A => Algebra.IsLocalIso A Z) (CommAlgCat.of A X))
    (hY : ObjectProperty.ind.{u}
      (fun Z : CommAlgCat.{u} A => Algebra.IsLocalIso A Z) (CommAlgCat.of A Y)) :
    ObjectProperty.ind.{u} (fun Z : CommAlgCat.{u} A => Algebra.IsLocalIso A Z)
      (CommAlgCat.of A (X × Y)) := by
  classical
  let P : ObjectProperty (CommAlgCat.{u} A) := fun Z => Algebra.IsLocalIso A Z
  rcases hX with ⟨I, hI, hIF, pX, hPX⟩
  rcases hY with ⟨J, hJ, hJF, pY, hPY⟩
  let : SmallCategory I := hI
  let : IsFiltered I := hIF
  let : SmallCategory J := hJ
  let : IsFiltered J := hJF
  let cX := pX.cocone
  let cY := pY.cocone
  have hcXType : IsColimit ((forget (CommAlgCat.{u} A)).mapCocone cX) :=
    isColimitOfPreserves (forget (CommAlgCat.{u} A)) pX.isColimit
  have hcYType : IsColimit ((forget (CommAlgCat.{u} A)).mapCocone cY) :=
    isColimitOfPreserves (forget (CommAlgCat.{u} A)) pY.isColimit
  let cProd := commAlgProductFunctor.mapCocone (productCocone cX cY)
  let F : (I × J) ⥤ CommAlgCat.{u} A :=
    (pX.diag.prod pY.diag) ⋙ commAlgProductFunctor
  have hType : IsColimit ((forget (CommAlgCat.{u} A)).mapCocone cProd) := by
    apply Types.FilteredColimit.isColimitOf
    · rintro ⟨x, y⟩
      obtain ⟨i, a, ha⟩ := Types.jointly_surjective_of_isColimit hcXType x
      obtain ⟨j, b, hb⟩ := Types.jointly_surjective_of_isColimit hcYType y
      exact ⟨(i, j), (a, b), Prod.ext ha.symm hb.symm⟩
    · rintro ⟨i, j⟩ ⟨i', j'⟩ ⟨a, b⟩ ⟨a', b'⟩ hab
      obtain ⟨k, f, g, hf⟩ :=
        (Types.FilteredColimit.isColimit_eq_iff _ hcXType).mp (congrArg Prod.fst hab)
      obtain ⟨l, f', g', hg⟩ :=
        (Types.FilteredColimit.isColimit_eq_iff _ hcYType).mp (congrArg Prod.snd hab)
      exact ⟨(k, l), (f, f'), (g, g'), Prod.ext hf hg⟩
  have hcolim : IsColimit cProd := by
    have hreflect : ReflectsColimit F (forget (CommAlgCat.{u} A)) :=
      reflectsColimit_of_reflectsIsomorphisms F (forget (CommAlgCat.{u} A))
    exact isColimitOfReflects (forget (CommAlgCat.{u} A)) hType
  have hStages : ∀ ij : I × J, P (F.obj ij) := by
    intro ij
    change Algebra.IsLocalIso A
      ((pX.diag.obj ij.1 : Type u) × (pY.diag.obj ij.2 : Type u))
    exact localIso_prod_of_localIso _ _ (hPX ij.1) (hPY ij.2)
  exact ⟨I × J, inferInstance, inferInstance, ⟨F, cProd.ι, hcolim⟩, hStages⟩

private theorem localIso_ind_isClosedUnderBinaryProducts :
    ObjectProperty.IsClosedUnderBinaryProducts
      (ObjectProperty.ind.{u}
        (fun Z : CommAlgCat.{u} A => Algebra.IsLocalIso A Z)) := by
  let P : ObjectProperty (CommAlgCat.{u} A) := fun Z => Algebra.IsLocalIso A Z
  apply ObjectProperty.IsClosedUnderLimitsOfShape.mk'
  rintro Z ⟨F, hF⟩
  let B : Type u := F.obj (Discrete.mk WalkingPair.left)
  let C : Type u := F.obj (Discrete.mk WalkingPair.right)
  have hB : P.ind.{u} (CommAlgCat.of A B) := hF (Discrete.mk WalkingPair.left)
  have hC : P.ind.{u} (CommAlgCat.of A C) := hF (Discrete.mk WalkingPair.right)
  have hBC := localIso_ind_prod (A := A) B C hB hC
  let S : WalkingPair → Type u := fun j => F.obj (Discrete.mk j)
  let eObjects : (∏ᶜ fun j : WalkingPair => F.obj (Discrete.mk j)) ≅
      ∏ᶜ fun j : WalkingPair => CommAlgCat.of A (S j) :=
    Pi.mapIso (fun j => CommAlgCat.isoMk (AlgEquiv.refl (R := A) (A₁ := S j)))
  let SULift : ULift.{u} WalkingPair → Type u := fun j => S j.down
  let eLift : (∏ᶜ fun j : ULift.{u} WalkingPair => CommAlgCat.of A (SULift j)) ≅
      ∏ᶜ fun j : WalkingPair => CommAlgCat.of A (S j) :=
    Pi.reindex Equiv.ulift (fun j : WalkingPair => CommAlgCat.of A (S j))
  let eProduct : (∏ᶜ fun j : WalkingPair => F.obj (Discrete.mk j)) ≅
      CommAlgCat.of A (∀ j : ULift.{u} WalkingPair, SULift j) :=
    eObjects ≪≫ eLift.symm ≪≫ commAlgCatPiIso (A := A) SULift
  let eAlgULift : (∀ j : ULift.{u} WalkingPair, SULift j) ≃ₐ[A] (B × C) := {
    toFun := fun f =>
      (f (ULift.up WalkingPair.left), f (ULift.up WalkingPair.right))
    invFun := fun p j => by
      cases j with
      | up j => cases j with
        | left => exact p.1
        | right => exact p.2
    left_inv := fun f => funext fun j => by cases j with | up j => cases j <;> rfl
    right_inv := fun _ => rfl
    map_mul' := fun _ _ => rfl
    map_add' := fun _ _ => rfl
    commutes' := fun a => by apply Prod.ext <;> simp [SULift, S, B, C] }
  let ePair : CommAlgCat.of A (∀ j : ULift.{u} WalkingPair, SULift j) ≅
      CommAlgCat.of A (B × C) := CommAlgCat.isoMk eAlgULift
  let eLimit : CommAlgCat.of A (∀ j : ULift.{u} WalkingPair, SULift j) ≅ limit F :=
    eProduct.symm ≪≫ Pi.isoLimit _
  exact P.ind.prop_of_iso (ePair.symm ≪≫ eLimit) hBC

private theorem localIso_ind_isClosedUnderTerminal :
    ObjectProperty.IsClosedUnderLimitsOfShape
      (ObjectProperty.ind.{u}
        (fun Z : CommAlgCat.{u} A => Algebra.IsLocalIso A Z))
      (Discrete.{0} PEmpty) := by
  let P : ObjectProperty (CommAlgCat.{u} A) := fun Z => Algebra.IsLocalIso A Z
  apply ObjectProperty.IsClosedUnderLimitsOfShape.mk'
  rintro Z ⟨F, hF⟩
  let T : CommAlgCat.{u} A := CommAlgCat.of A PUnit
  let : Algebra.IsLocalIso A PUnit := {
    exists_notMem_isStandardOpenImmersion := by
      intro q hq
      have hone : (1 : PUnit) ∈ q := by
        rw [Subsingleton.elim (1 : PUnit) (0 : PUnit)]
        exact q.zero_mem
      exact (hq.ne_top ((Ideal.eq_top_iff_one q).2 hone)).elim }
  have hT : P.ind.{u} T := P.le_ind _ (inferInstanceAs (Algebra.IsLocalIso A PUnit))
  have ht : IsTerminal T := IsTerminal.ofUniqueHom
    (fun X => CommAlgCat.ofHom {
      toRingHom := {
        toFun := fun _ => PUnit.unit
        map_one' := rfl
        map_mul' := fun _ _ => rfl
        map_zero' := rfl
        map_add' := fun _ _ => rfl }
      commutes' := fun _ => rfl })
    (fun _ _ => CommAlgCat.hom_ext (AlgHom.ext fun _ => Subsingleton.elim _ _))
  exact P.ind.prop_of_iso ((isLimitEquivIsTerminalOfIsEmpty (CommAlgCat.{u} A)
    (limit.cone F) (limit.isLimit F)).uniqueUpToIso ht).symm hT

private theorem stratificationRing_indZariski (E : Finset A) :
    ObjectProperty.ind.{u} (fun C : CommAlgCat.{u} A => Algebra.IsLocalIso A C)
      (CommAlgCat.of A (stratificationRing E)) := by
  classical
  let idx : Type u := {E' : Finset A // E' ⊆ E}
  let : Fintype idx := stratumIndexFintype E
  let S : idx → Type u := fun i =>
    localizationRing (stratumIdeal E i) (stratumOpenElement i.val)
  let P : ObjectProperty (CommAlgCat.{u} A) := fun C => Algebra.IsLocalIso A C
  have hstage : ∀ i : idx, P.ind.{u} (CommAlgCat.of A (S i)) := by
    intro i
    change ObjectProperty.ind.{u}
      (fun C : CommAlgCat.{u} A => Algebra.IsLocalIso A C)
      (CommAlgCat.of A (Localization
        (localizationSubmonoid (stratumIdeal E i) (stratumOpenElement i.val))))
    exact Algebra.isIndZariski_iff.mp (isIndZariski_localization (A := A)
      (localizationSubmonoid (stratumIdeal E i) (stratumOpenElement i.val)))
  let : ObjectProperty.IsClosedUnderFiniteProducts P :=
    localIso_isClosedUnderFiniteProducts
  let : P.ind.IsClosedUnderBinaryProducts :=
    localIso_ind_isClosedUnderBinaryProducts (A := A)
  let : P.ind.IsClosedUnderLimitsOfShape (Discrete.{0} PEmpty) :=
    localIso_ind_isClosedUnderTerminal (A := A)
  let : ObjectProperty.IsClosedUnderFiniteProducts P.ind :=
    ObjectProperty.IsClosedUnderFiniteProducts.mk' (P := P.ind)
  change P.ind.{u} (CommAlgCat.of A (∀ i : {E' : Finset A // E' ⊆ E},
    localizationRing (stratumIdeal E i) (stratumOpenElement i.val)))
  exact (P.ind.{u}.prop_iff_of_iso (commAlgCatPiIso (A := A) S)).mp (P.ind.prop_pi _ hstage)

/-- The canonical map to the stratification colimit is ind-Zariski. -/
theorem stratificationColimit_isIndZariski :
    IsIndZariski.{u, u, u} A (stratificationColimitRing (A := A)) := by
  classical
  let : Nonempty (Finset A) := ⟨∅⟩
  let pres : ColimitPresentation (Finset A)
      (CommAlgCat.of A (stratificationColimitRing (A := A))) :=
    ⟨stratificationDiagram (A := A), (stratificationColimitCocone (A := A)).ι,
      stratificationColimitCocone_isColimit (A := A)⟩
  have hind : (ObjectProperty.ind.{u}
      (fun C : CommAlgCat.{u} A => Algebra.IsLocalIso A C)).ind.{u}
      (CommAlgCat.of A (stratificationColimitRing (A := A))) :=
    ObjectProperty.of_essentiallySmall_index pres (stratificationRing_indZariski (A := A))
  rw [ObjectProperty.ind_ind (localIso_isFinitelyPresentable.{u, u} A)] at hind
  change ObjectProperty.ind.{u}
    (fun C : CommAlgCat.{u} A => Algebra.IsLocalIso A C)
    (CommAlgCat.of A (ULift.{u} (stratificationColimitRing (A := A))))
  exact ((ObjectProperty.ind.{u}
    (fun C : CommAlgCat.{u} A => Algebra.IsLocalIso A C)).prop_iff_of_iso
      (CommAlgCat.isoMk (ULift.algEquiv (R := A)
        (A := stratificationColimitRing (A := A))))).mpr hind

/-- The canonical map to the stratification colimit is faithfully flat. -/
theorem stratificationColimit_faithfullyFlat :
    (stratificationColimitAlgebraMap (A := A)).FaithfullyFlat := by
  classical
  let : Nonempty (Finset A) := ⟨∅⟩
  rw [← stratificationColimit_algebraMap_eq_arbitrary]
  exact faithfullyFlat_directLimit_of_faithfullyFlat A
    (fun E : Finset A => stratificationRing E)
    (fun E₁ E₂ h => stratificationRingMap E₁ E₂ h)
    stratificationRingMap_comp_algebraMap_eq
    stratificationAlgebraMap_faithfullyFlat

/-- **Stacks 0975**, part (1): the canonical map `A → A_w` from a commutative ring to its
stratification colimit is ind-Zariski and faithfully flat. -/
@[stacks 0975 "ind_zariski_faithfully_flat"]
theorem stratificationColimit_isIndZariski_and_faithfullyFlat :
    IsIndZariski.{u, u, u} A (stratificationColimitRing (A := A)) ∧
      (stratificationColimitAlgebraMap (A := A)).FaithfullyFlat :=
  ⟨stratificationColimit_isIndZariski, stratificationColimit_faithfullyFlat⟩

end AlgebraicGeometry.ProEtale

end
