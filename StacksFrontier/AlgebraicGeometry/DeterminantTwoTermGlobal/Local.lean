module

public import StacksFrontier.AlgebraicGeometry.DeterminantTwoTermAffine
public import StacksFrontier.AlgebraicGeometry.Perfect.AffinePullbackComparisonCocycle
public import StacksFrontier.Homology.TwoTermComplex.DeterminantBaseChangeComp
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The determinant of a two-term perfect complex along morphisms from affine schemes

Let `X` be a scheme and `K` a perfect object of `D(𝒪_X)` of Tor amplitude in `[-1, 0]`. For every
morphism `u : Spec A ⟶ X` the derived pullback `Lu^*K` is perfect of Tor amplitude in `[-1, 0]`
on `Spec A`, hence the sheaf associated with a perfect object `M_u` of `D(A)` of Tor amplitude in
`[-1, 0]`, and it has a determinant `det(M_u)`, an invertible `A`-module, by More on Algebra,
Section 0FJI. This file records how these depend on `u`: for a ring map `g : A → B` and
`u' = Spec(g) ≫ u`, there is a canonical isomorphism `B ⊗ᴸ_A M_u ≅ M_{u'}` (Stacks 08DW and
Stacks 0D5S), these are compatible with composition, and the induced maps of determinants
`det(M_u) → det(M_{u'})` exhibit `det(M_{u'})` as `B ⊗_A det(M_u)`, compose, and preserve the
canonical element of a rank-zero object. Along a morphism of schemes `f : X ⟶ Y`, the local data
of `Lf^*K` along `u` are those of `K` along `u ≫ f`.

## Main definitions

* `AlgebraicGeometry.DeterminantTwoTerm.localComplex`: the complex `M_u`.
* `AlgebraicGeometry.DeterminantTwoTerm.transitionIso`: `B ⊗ᴸ_A M_u ≅ M_{u'}`.
* `AlgebraicGeometry.DeterminantTwoTerm.localDet` and `localDetMap`: `det(M_u)` and the map
  `det(M_u) → det(M_{u'})`.
-/

@[expose] public noncomputable section

universe u

open CategoryTheory TwoTermDeterminant
open AlgebraicGeometry.StandardModel
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces (derivedPullback)

namespace AlgebraicGeometry.DeterminantTwoTerm

attribute [local instance 10000] HasDerivedCategory.standard

variable {X : Scheme.{u}}

/-- The perfect complex of `A`-modules of Tor amplitude in `[-1, 0]` whose associated sheaf is
the derived pullback of `K` along `u : Spec A ⟶ X`. -/
def localComplex (K : PerfectTwoTermAmplitude X) {A : CommRingCat.{u}} (u : Spec A ⟶ X) :
    PerfectTwoTermComplex A :=
  sourceComplex A (derivedPullbackObj u K)

/-- The sheaf associated with `localComplex K u` is `Lu^*K`. -/
def localComplexIso (K : PerfectTwoTermAmplitude X) {A : CommRingCat.{u}} (u : Spec A ⟶ X) :
    (tilde.functor A).mapDerivedCategory.obj (localComplex K u).obj ≅ (dpb u).obj K.obj :=
  (IsPerfectTwoTermAmplitude (Spec A)).ι.mapIso (tildeSourceComplexIso A (derivedPullbackObj u K))

/-- The composition isomorphism of Stacks 0D5S along a factorisation of morphisms of schemes, with
both derived categories in the scheme spelling. -/
def fac {V W Z : Scheme.{u}} (p : V ⟶ W) (t : W ⟶ Z) (q : V ⟶ Z) (hq : p ≫ t = q)
    (M : DerivedCategory Z.Modules) : (dpb p).obj ((dpb t).obj M) ≅ (dpb q).obj M :=
  (Stacks.DerivedPullback.schemeFactorIso p t q hq).app M

/-- The affine comparison morphism `StandardModel.cmp g M` is an isomorphism. -/
instance isIso_cmp {A B : CommRingCat.{u}} (g : A ⟶ B) (M : DerivedCategory (ModuleCat.{u} A)) :
    IsIso (StandardModel.cmp g M) :=
  inferInstanceAs (IsIso ((affinePullbackComparison A B g).hom.app M))

/-- **The transition isomorphism** `B ⊗ᴸ_A M_u ≅ M_{u'}` for `Spec(g) ≫ u = u'`: the affine
comparison of Stacks 08DW followed by the composition isomorphism of Stacks 0D5S, read back in
`D(B)` through the full faithfulness of derived sheafification on `Spec B`. -/
def transitionIso (K : PerfectTwoTermAmplitude X) {A B : CommRingCat.{u}} (g : A ⟶ B)
    (u : Spec A ⟶ X) (u' : Spec B ⟶ X) (h : Spec.map g ≫ u = u') :
    (Lext g.hom).obj (localComplex K u).obj ≅ (localComplex K u').obj :=
  (mapDerivedCategoryFullyFaithful B).preimageIso
    ((asIso (StandardModel.cmp g (localComplex K u).obj)).symm ≪≫
      (dpb (Spec.map g)).mapIso (localComplexIso K u) ≪≫
      fac (Spec.map g) u u' h K.obj ≪≫ (localComplexIso K u').symm)

/-- The sheaf associated with the transition isomorphism `transitionIso K g u u' h` is the
composite of the inverse affine comparison, the pullback of `localComplexIso K u`, the composition
isomorphism `fac`, and the inverse of `localComplexIso K u'`. -/
theorem tilde_map_transitionIso_hom (K : PerfectTwoTermAmplitude X) {A B : CommRingCat.{u}}
    (g : A ⟶ B) (u : Spec A ⟶ X) (u' : Spec B ⟶ X) (h : Spec.map g ≫ u = u') :
    (tilde.functor B).mapDerivedCategory.map (transitionIso K g u u' h).hom =
      inv (StandardModel.cmp g (localComplex K u).obj) ≫
        (dpb (Spec.map g)).map (localComplexIso K u).hom ≫
        (fac (Spec.map g) u u' h K.obj).hom ≫ (localComplexIso K u').inv := by
  simp only [transitionIso, Functor.FullyFaithful.preimageIso_hom,
    Functor.FullyFaithful.map_preimage, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom,
    asIso_inv]

/-- The composition morphism `fcomp g k M` of derived pullbacks along `Spec` is an isomorphism. -/
instance isIso_fcomp {A B C : CommRingCat.{u}} (g : A ⟶ B) (k : B ⟶ C)
    (M : DerivedCategory (Spec A).Modules) : IsIso (fcomp g k M) :=
  inferInstanceAs (IsIso ((specDerivedPullbackCompIso g k).hom.app M))

/-- **Associativity of the composition isomorphism of Stacks 0D5S**, for morphisms of schemes. -/
theorem schemeFactorIso_assoc {V W Y Z : Scheme.{u}} (p : V ⟶ W) (t : W ⟶ Y) (a : Y ⟶ Z)
    (b : W ⟶ Z) (q : V ⟶ Y) (c : V ⟶ Z) (hb : t ≫ a = b) (hq : p ≫ t = q) (hc : q ≫ a = c)
    (hpb : p ≫ b = c)
    (M : DerivedCategory (SheafOfModules.{u} (structureSheafRing Z.toRingedSpace))) :
    ((Stacks.DerivedPullback.schemeFactorIso p t q hq).app
        ((derivedPullback a.toLRSHom.toShHom).obj M)).hom ≫
        ((Stacks.DerivedPullback.schemeFactorIso q a c hc).app M).hom =
      (derivedPullback p.toLRSHom.toShHom).map
          ((Stacks.DerivedPullback.schemeFactorIso t a b hb).app M).hom ≫
        ((Stacks.DerivedPullback.schemeFactorIso p b c hpb).app M).hom :=
  congrArg Iso.hom (Stacks.DerivedPullback.factorIso_assoc p.toLRSHom.toShHom t.toLRSHom.toShHom
    a.toLRSHom.toShHom b.toLRSHom.toShHom q.toLRSHom.toShHom c.toLRSHom.toShHom
    (congrArg (fun m : W ⟶ Z ↦ m.toLRSHom.toShHom) hb)
    (congrArg (fun m : V ⟶ Y ↦ m.toLRSHom.toShHom) hq)
    (congrArg (fun m : V ⟶ Z ↦ m.toLRSHom.toShHom) hc)
    (congrArg (fun m : V ⟶ Z ↦ m.toLRSHom.toShHom) hpb) M)

/-- Associativity of the composition isomorphisms `fac` of derived pullbacks. -/
theorem fac_assoc {V W Y Z : Scheme.{u}} (p : V ⟶ W) (t : W ⟶ Y) (a : Y ⟶ Z)
    (b : W ⟶ Z) (q : V ⟶ Y) (c : V ⟶ Z) (hb : t ≫ a = b) (hq : p ≫ t = q) (hc : q ≫ a = c)
    (hpb : p ≫ b = c) (M : DerivedCategory Z.Modules) :
    (fac p t q hq ((dpb a).obj M)).hom ≫ (fac q a c hc M).hom =
      (dpb p).map (fac t a b hb M).hom ≫ (fac p b c hpb M).hom :=
  schemeFactorIso_assoc p t a b q c hb hq hc hpb M

/-- The composition isomorphism `fac p t q hq` is natural in the object of `D(𝒪_Z)`. -/
theorem fac_naturality {V W Z : Scheme.{u}} (p : V ⟶ W) (t : W ⟶ Z) (q : V ⟶ Z)
    (hq : p ≫ t = q) {M N : DerivedCategory Z.Modules} (φ : M ⟶ N) :
    (dpb p).map ((dpb t).map φ) ≫ (fac p t q hq N).hom = (fac p t q hq M).hom ≫ (dpb q).map φ :=
  (Stacks.DerivedPullback.schemeFactorIso p t q hq).hom.naturality φ

/-- The composition morphism `fcomp g k M` is the composition isomorphism `fac` for
`Spec(g ≫ k) = Spec(k) ≫ Spec(g)`. -/
theorem fcomp_eq {A B C : CommRingCat.{u}} (g : A ⟶ B) (k : B ⟶ C)
    (M : DerivedCategory (Spec A).Modules) :
    fcomp g k M =
      (fac (Spec.map k) (Spec.map g) (Spec.map (g ≫ k)) (Spec.map_comp g k).symm M).hom :=
  rfl

/-- The composition isomorphism of derived extension of scalars, read through derived
sheafification. -/
theorem tilde_map_compIso_inv {A B C : CommRingCat.{u}} (g : A ⟶ B) (k : B ⟶ C)
    (M : DerivedCategory (ModuleCat.{u} A)) :
    (tilde.functor C).mapDerivedCategory.map (compIso g.hom k.hom M).inv =
      inv (StandardModel.cmp (g ≫ k) M) ≫
        inv (fcomp g k ((tilde.functor A).mapDerivedCategory.obj M)) ≫
        (dpb (Spec.map k)).map (StandardModel.cmp g M) ≫
        StandardModel.cmp k ((Lext g.hom).obj M) := by
  have h := cmp_comp g k M
  have he : extComp g k M = (compIso g.hom k.hom M).hom := rfl
  rw [IsIso.eq_inv_comp, IsIso.eq_inv_comp, ← Category.assoc, ← h, he]
  simp only [Category.assoc, ← Functor.map_comp, Iso.hom_inv_id, CategoryTheory.Functor.map_id,
    Category.comp_id]

/-- Derived extension of scalars of a morphism, read through derived sheafification. -/
private theorem tilde_map_lext_map {A B : CommRingCat.{u}} (g : A ⟶ B)
    {M N : DerivedCategory (ModuleCat.{u} A)} (φ : M ⟶ N) :
    (tilde.functor B).mapDerivedCategory.map ((Lext g.hom).map φ) =
      inv (StandardModel.cmp g M) ≫
        (dpb (Spec.map g)).map ((tilde.functor A).mapDerivedCategory.map φ) ≫
          StandardModel.cmp g N := by
  rw [IsIso.eq_inv_comp]
  exact cmp_naturality g φ

/-- **The transition isomorphisms compose.** For `Spec(g) ≫ u = u'` and `Spec(k) ≫ u' = u''`, the
transition isomorphism of `g ≫ k` is that of `g`, base changed along `k`, followed by that of `k`,
up to the composition isomorphism of derived extension of scalars. -/
theorem transitionIso_comp (K : PerfectTwoTermAmplitude X) {A B C : CommRingCat.{u}} (g : A ⟶ B)
    (k : B ⟶ C) (u : Spec A ⟶ X) (u' : Spec B ⟶ X) (u'' : Spec C ⟶ X)
    (h : Spec.map g ≫ u = u') (h' : Spec.map k ≫ u' = u'') (h'' : Spec.map (g ≫ k) ≫ u = u'') :
    (transitionIso K (g ≫ k) u u'' h'').hom =
      (compIso g.hom k.hom (localComplex K u).obj).inv ≫
        (Lext k.hom).map (transitionIso K g u u' h).hom ≫ (transitionIso K k u' u'' h').hom := by
  apply (mapDerivedCategoryFullyFaithful C).map_injective
  rw [Functor.map_comp, Functor.map_comp, tilde_map_lext_map, tilde_map_compIso_inv,
    tilde_map_transitionIso_hom, tilde_map_transitionIso_hom, tilde_map_transitionIso_hom]
  simp only [Category.assoc, Functor.map_comp, Functor.map_inv, IsIso.hom_inv_id_assoc]
  rw [← Functor.map_comp_assoc (dpb (Spec.map k)) (localComplexIso K u').inv, Iso.inv_hom_id,
    CategoryTheory.Functor.map_id, Category.id_comp]
  congr 1
  rw [IsIso.eq_inv_comp, reassoc_of% (fcomp_naturality g k (localComplexIso K u).hom)]
  congr 1
  rw [← Category.assoc, ← Category.assoc]
  congr 1
  rw [fcomp_eq]
  exact fac_assoc (Spec.map k) (Spec.map g) u u' (Spec.map (g ≫ k)) u'' h
    (Spec.map_comp g k).symm h'' h' K.obj

/-! ### Along a morphism of schemes -/

section Pullback

variable {Y : Scheme.{u}} (f : X ⟶ Y) (K : PerfectTwoTermAmplitude Y)

/-- The derived pullback `Lf^*K`, as an object of the source category of the determinant on `X`
(Stacks 0FJY, first assertion: `isPerfectTwoTermAmplitude_derivedPullback`). -/
@[sga "6 I 4.19.2" "special case"]
abbrev pullbackObj : PerfectTwoTermAmplitude X :=
  ⟨(dpb f).obj K.obj, isPerfectTwoTermAmplitude_derivedPullback f K.obj K.property⟩

/-- The underlying object of `pullbackObj f K` is `Lf^*K`. -/
@[simp]
theorem pullbackObj_obj : (pullbackObj f K).obj = (dpb f).obj K.obj := rfl

/-- The local avatar of `Lf^*K` along `u` is the local avatar of `K` along `u ≫ f`. -/
def pullbackLocalIso {A : CommRingCat.{u}} (u : Spec A ⟶ X) :
    (localComplex (pullbackObj f K) u).obj ≅ (localComplex K (u ≫ f)).obj :=
  (mapDerivedCategoryFullyFaithful A).preimageIso
    (localComplexIso (pullbackObj f K) u ≪≫ fac u f (u ≫ f) rfl K.obj ≪≫
      (localComplexIso K (u ≫ f)).symm)

/-- The sheaf associated with `pullbackLocalIso f K u` is the composite of
`localComplexIso (pullbackObj f K) u`, the composition isomorphism `fac`, and the inverse of
`localComplexIso K (u ≫ f)`. -/
theorem tilde_map_pullbackLocalIso_hom {A : CommRingCat.{u}} (u : Spec A ⟶ X) :
    (tilde.functor A).mapDerivedCategory.map (pullbackLocalIso f K u).hom =
      (localComplexIso (pullbackObj f K) u).hom ≫ (fac u f (u ≫ f) rfl K.obj).hom ≫
        (localComplexIso K (u ≫ f)).inv := by
  simp only [pullbackLocalIso, Functor.FullyFaithful.preimageIso_hom,
    Functor.FullyFaithful.map_preimage, Iso.trans_hom, Iso.symm_hom]

/-- **The comparison with the pullback is compatible with the transition isomorphisms.** -/
theorem pullbackLocalIso_transitionIso {A B : CommRingCat.{u}} (g : A ⟶ B) (u : Spec A ⟶ X)
    (u' : Spec B ⟶ X) (h : Spec.map g ≫ u = u') (h₂ : Spec.map g ≫ u ≫ f = u' ≫ f) :
    (Lext g.hom).map (pullbackLocalIso f K u).hom ≫ (transitionIso K g (u ≫ f) (u' ≫ f) h₂).hom =
      (transitionIso (pullbackObj f K) g u u' h).hom ≫ (pullbackLocalIso f K u').hom := by
  apply (mapDerivedCategoryFullyFaithful B).map_injective
  rw [Functor.map_comp, Functor.map_comp, tilde_map_lext_map, tilde_map_transitionIso_hom,
    tilde_map_transitionIso_hom, tilde_map_pullbackLocalIso_hom, tilde_map_pullbackLocalIso_hom]
  simp only [Category.assoc, Functor.map_comp, IsIso.hom_inv_id_assoc, Iso.inv_hom_id_assoc]
  rw [← Functor.map_comp_assoc (dpb (Spec.map g)) (localComplexIso K (u ≫ f)).inv, Iso.inv_hom_id,
    CategoryTheory.Functor.map_id, Category.id_comp]
  congr 2
  rw [← reassoc_of% (fac_assoc (Spec.map g) u f (u ≫ f) u' (u' ≫ f) rfl h rfl h₂ K.obj)]

end Pullback

/-! ### The local determinants -/

section Det

variable (K : PerfectTwoTermAmplitude X)

/-- The determinant `det(M_u)` of the local avatar of `K` along `u`, an invertible `A`-module. -/
abbrev localDet {A : CommRingCat.{u}} (u : Spec A ⟶ X) : ModuleCat.{u} A :=
  ((det A).obj ⟨localComplex K u⟩).of.obj

/-- The map of local determinants along `Spec(g) ≫ u = u'`, semilinear over `g`. -/
def localDetMap {A B : CommRingCat.{u}} (g : A ⟶ B) (u : Spec A ⟶ X) (u' : Spec B ⟶ X)
    (h : Spec.map g ≫ u = u') : localDet K u →ₛₗ[g.hom] localDet K u' :=
  baseChangeMap g.hom (localComplex K u) (localComplex K u') (transitionIso K g u u' h)

/-- The map `localDetMap K g u u' h` exhibits `det(M_{u'})` as the base change
`B ⊗_A det(M_u)`. -/
theorem isBaseChangeAlong_localDetMap {A B : CommRingCat.{u}} (g : A ⟶ B) (u : Spec A ⟶ X)
    (u' : Spec B ⟶ X) (h : Spec.map g ≫ u = u') :
    IsBaseChangeAlong g.hom (localDetMap K g u u' h) :=
  isBaseChangeAlong_baseChangeMap _ _

/-- **The maps of local determinants compose.** -/
theorem localDetMap_comp {A B C : CommRingCat.{u}} (g : A ⟶ B) (k : B ⟶ C) (u : Spec A ⟶ X)
    (u' : Spec B ⟶ X) (u'' : Spec C ⟶ X) (h : Spec.map g ≫ u = u') (h' : Spec.map k ≫ u' = u'')
    (h'' : Spec.map (g ≫ k) ≫ u = u'') (x : localDet K u) :
    localDetMap K (g ≫ k) u u'' h'' x = localDetMap K k u' u'' h' (localDetMap K g u u' h x) := by
  have he : transitionIso K (g ≫ k) u u'' h'' =
      (compIso g.hom k.hom (localComplex K u).obj).symm ≪≫
        (Lext k.hom).mapIso (transitionIso K g u u' h) ≪≫ transitionIso K k u' u'' h' :=
    Iso.ext (transitionIso_comp K g k u u' u'' h h' h'')
  rw [localDetMap, he]
  exact baseChangeMap_comp g.hom k.hom _ _ x

/-- Rank zero, for the local avatar along `u`. -/
abbrev IsLocallyRankZero {A : CommRingCat.{u}} (u : Spec A ⟶ X) : Prop :=
  IsRankZero (localComplex K u).obj

/-- If the local complex of `K` along `u` has rank zero, so does the one along
`u' = Spec(g) ≫ u`. -/
theorem isLocallyRankZero_of_transition {A B : CommRingCat.{u}} (g : A ⟶ B) (u : Spec A ⟶ X)
    (u' : Spec B ⟶ X) (h : Spec.map g ≫ u = u') (hu : IsLocallyRankZero K u) :
    IsLocallyRankZero K u' :=
  TwoTermDeterminant.isRankZero_of_iso g.hom hu (transitionIso K g u u' h)

/-- **The maps of local determinants preserve the canonical element.** -/
theorem localDetMap_delta {A B : CommRingCat.{u}} (g : A ⟶ B) (u : Spec A ⟶ X)
    (u' : Spec B ⟶ X) (h : Spec.map g ≫ u = u') (hu : IsLocallyRankZero K u)
    (hu' : IsLocallyRankZero K u') :
    localDetMap K g u u' h (delta (localComplex K u) hu) = delta (localComplex K u') hu' :=
  baseChangeMap_delta _ _ _ _

end Det

end AlgebraicGeometry.DeterminantTwoTerm

end
