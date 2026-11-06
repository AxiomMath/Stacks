module

public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import Mathlib.AlgebraicGeometry.Stalk
public import StacksFrontier.RingTheory.Henselian.StrictHenselization
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.EtaleFundamental.ChangeBasePoint
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.GaloisCategory.InertiaDiagram
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.StrictlyHenselianSplitting
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Specialization maps between fundamental groups of geometric fibres

Let `f : X ⟶ S` be proper with geometrically connected fibres and let `s' ⇝ s` be a
specialization of points of `S`. Writing `A` for the strict henselization of `𝒪_{S,s}` relative
to a separable closure of `κ(s)` inside `κ(s̄)`, a factorization of the geometric point `s̄'`
through `Spec A` yields a composite
`π₁(X_{s̄'}) → π₁(X_A) = π₁(X_{s̄})`, the *specialization map*. It depends on the chosen
factorization, so it is not a function of `s' ⇝ s` alone; `AlgebraicGeometry.IsSpecializationMap`
is the predicate recording that a given continuous homomorphism arises this way.

## Main definitions

* `AlgebraicGeometry.fiberOverGeometricPoint` — the fibre of a morphism over a geometric point.
* `AlgebraicGeometry.fiberOverGeometricPointMap` — the map from a geometric fibre into a base
  change,
  determined by a factorization of the geometric point.
* `AlgebraicGeometry.pullbackBaseChangeMap` — the map between two base changes of a morphism
  induced by a morphism of the base schemes.
* `AlgebraicGeometry.fiberFunctorMapCompIso` — the identification of the two fibre functors
  attached to the image of a geometric point under a composite.
* `AlgebraicGeometry.fiberFunctorTransportIso` — a fibre-functor isomorphism transported along
  base change.
* `AlgebraicGeometry.IsSpecializationMap` — the predicate that a continuous homomorphism of
  étale fundamental groups is a specialization map.

## Main results

* `AlgebraicGeometry.isSpecializationMap_comp` — a composite of specialization maps is a
  specialization map.
* `AlgebraicGeometry.etaleFundamentalGroupMulEquiv_transportIso` — the induced map on
  fundamental groups intertwines a base-point change with its transport along base change.
* `AlgebraicGeometry.etaleFundamentalGroupMulEquiv_mapCompIso` — the induced map of a composite
  is the composite of the induced maps, with the base-point identification made explicit.
* `AlgebraicGeometry.geometricFiberMap_comp_pullbackBaseChangeMap` — factoring a geometric point
  through an intermediate base agrees with factoring it directly.

## Implementation notes

The source suppresses geometric base points, so its fundamental groups are determined only up to
inner automorphism. Here the base points of the geometric fibres are explicit arguments, and the
base-point change on `X_A` needed to compare the two incoming maps is carried by a fibre-functor
isomorphism inside the predicate.

The defining equation of a specialization map is written in the forward direction, as
`etaleFundamentalGroupMap i x ∘ sp = etaleFundamentalGroupMulEquiv t ∘ etaleFundamentalGroupMap
i' x'`, rather than by inverting `etaleFundamentalGroupMap i x`. Since base change along `i` is
an equivalence — part of the recorded data — that map is injective, so the equation pins `sp`
exactly as a formula with the inverse would, while needing only the canonical maps.

`AlgebraicGeometry.etaleFundamentalGroupMap_comp` compares two propositionally equal induced
base points and is therefore stated as a heterogeneous equality;
`AlgebraicGeometry.fiberFunctorMapCompIso` names that identification so the comparison can be
rewritten with an ordinary equation.

## References

* [Stacks Project, Tag 0C0L](https://stacks.math.columbia.edu/tag/0C0L)
* [Stacks Project, Tag 0BND](https://stacks.math.columbia.edu/tag/0BND)
* [Stacks Project, Tag 08HR](https://stacks.math.columbia.edu/tag/08HR)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits IsLocalRing Stacks.FundamentalGroup

open scoped TensorProduct

universe u

namespace AlgebraicGeometry

variable {X Y Z S : Scheme.{u}}

/-! ### Base-point bookkeeping for the induced maps -/

/-- The identification of the two geometric fibre functors attached to the two descriptions of
the image of a geometric point under a composite. -/
def fiberFunctorMapCompIso (f : X ⟶ Y) (g : Y ⟶ Z) (x : GeometricPoint X) :
    finiteEtaleFiberFunctor (x.map (f ≫ g)) ≅ finiteEtaleFiberFunctor ((x.map f).map g) :=
  eqToIso (by rw [GeometricPoint.map_map])

/-- The map induced by a composite is the composite of the induced maps, compared through
`AlgebraicGeometry.fiberFunctorMapCompIso`. -/
theorem etaleFundamentalGroupMulEquiv_mapCompIso [ConnectedSpace X] [ConnectedSpace Y]
    [ConnectedSpace Z] (f : X ⟶ Y) (g : Y ⟶ Z) (x : GeometricPoint X)
    (σ : EtaleFundamentalGroup X x) :
    etaleFundamentalGroupMulEquiv (fiberFunctorMapCompIso f g x)
        (etaleFundamentalGroupMap (f ≫ g) x σ)
      = etaleFundamentalGroupMap g (x.map f) (etaleFundamentalGroupMap f x σ) := by
  have h := etaleFundamentalGroupMap_comp f g x σ
  cases GeometricPoint.map_map f g x
  rw [eq_of_heq h]
  simp only [fiberFunctorMapCompIso, etaleFundamentalGroupMulEquiv]
  rfl

/-- Transport along a composite of fibre-functor isomorphisms is the composite of the
transports. -/
theorem etaleFundamentalGroupMulEquiv_trans [ConnectedSpace X] {x y z : GeometricPoint X}
    (t : finiteEtaleFiberFunctor x ≅ finiteEtaleFiberFunctor y)
    (s : finiteEtaleFiberFunctor y ≅ finiteEtaleFiberFunctor z)
    (σ : EtaleFundamentalGroup X x) :
    etaleFundamentalGroupMulEquiv (t ≪≫ s) σ
      = etaleFundamentalGroupMulEquiv s (etaleFundamentalGroupMulEquiv t σ) := by
  apply Aut.ext
  apply Iso.ext
  apply NatTrans.ext
  funext V
  rfl

/-- The component of a transported automorphism at a point carried across by the fibre-functor
isomorphism. -/
theorem etaleFundamentalGroupMulEquiv_app_apply [ConnectedSpace X] {x y : GeometricPoint X}
    (t : finiteEtaleFiberFunctor x ≅ finiteEtaleFiberFunctor y)
    (σ : EtaleFundamentalGroup X x) (V : FiniteEtaleOver X) (z : finiteEtaleFiber x V) :
    ((etaleFundamentalGroupMulEquiv t σ).asIso.app V).hom (t.hom.app V z)
      = t.hom.app V ((σ.asIso.app V).hom z) :=
  conjAut_app_apply t σ V z

/-- An isomorphism of the geometric fibre functors at two points of `X` transported along a
morphism `f : X ⟶ Y`, through the fibre projections of base change along `f`. -/
def fiberFunctorTransportIso (f : X ⟶ Y) {x y : GeometricPoint X}
    (t : finiteEtaleFiberFunctor x ≅ finiteEtaleFiberFunctor y) :
    finiteEtaleFiberFunctor (x.map f) ≅ finiteEtaleFiberFunctor (y.map f) :=
  (finiteEtaleFiberProjectionIso f x).symm ≪≫
    Functor.isoWhiskerLeft (finiteEtaleBaseChange f) t ≪≫ finiteEtaleFiberProjectionIso f y

/-- The transported isomorphism acts on fibre projections by applying the original isomorphism
upstairs. -/
theorem fiberFunctorTransportIso_hom_app (f : X ⟶ Y) {x y : GeometricPoint X}
    (t : finiteEtaleFiberFunctor x ≅ finiteEtaleFiberFunctor y) (V : FiniteEtaleOver Y)
    (p : finiteEtaleFiber x ((finiteEtaleBaseChange f).obj V)) :
    (fiberFunctorTransportIso f t).hom.app V (finiteEtaleFiberProjection f x V p)
      = finiteEtaleFiberProjection f y V (t.hom.app _ p) := by
  show finiteEtaleFiberProjection f y V
    (t.hom.app _ ((finiteEtaleFiberProjectionEquiv f x V).symm
      ((finiteEtaleFiberProjectionEquiv f x V) p))) = _
  rw [Equiv.symm_apply_apply]

/-- A change of geometric base point commutes with the map induced by a morphism, the
fibre-functor isomorphism downstairs being the transport of the one upstairs. -/
theorem etaleFundamentalGroupMulEquiv_transportIso [ConnectedSpace X] [ConnectedSpace Y]
    (f : X ⟶ Y) {x y : GeometricPoint X}
    (t : finiteEtaleFiberFunctor x ≅ finiteEtaleFiberFunctor y)
    (σ : EtaleFundamentalGroup X x) :
    etaleFundamentalGroupMulEquiv (fiberFunctorTransportIso f t)
        (etaleFundamentalGroupMap f x σ)
      = etaleFundamentalGroupMap f y (etaleFundamentalGroupMulEquiv t σ) := by
  apply Aut.ext
  apply Iso.ext
  apply NatTrans.ext
  funext V
  ext q
  obtain ⟨q, rfl⟩ := (asIso ((fiberFunctorTransportIso f t).hom.app V)).toEquiv.surjective q
  obtain ⟨q, rfl⟩ := (finiteEtaleFiberProjectionEquiv f x V).surjective q
  show ((etaleFundamentalGroupMulEquiv (fiberFunctorTransportIso f t)
      (etaleFundamentalGroupMap f x σ)).asIso.app V).hom
      ((fiberFunctorTransportIso f t).hom.app V (finiteEtaleFiberProjection f x V q))
    = ((etaleFundamentalGroupMap f y (etaleFundamentalGroupMulEquiv t σ)).asIso.app V).hom
      ((fiberFunctorTransportIso f t).hom.app V (finiteEtaleFiberProjection f x V q))
  rw [etaleFundamentalGroupMulEquiv_app_apply,
    ← etaleFundamentalGroupMap_finiteEtaleFiberProjection,
    fiberFunctorTransportIso_hom_app, fiberFunctorTransportIso_hom_app,
    ← etaleFundamentalGroupMap_finiteEtaleFiberProjection,
    etaleFundamentalGroupMulEquiv_app_apply]


/-! ### Lifting residue-field points along an ind-étale algebra

The source's cited input is Tag 08HR: a point of an ind-étale algebra valued in a residue field
lifts uniquely to the henselian local ring. The form needed here prescribes the point through a
larger field, so the first two lemmas descend such a point to the residue field, using that an
étale algebra over a separably closed field is a product of copies of it.
-/

open scoped Classical in
/-- A point of a finite product of finite separable field extensions of a separably closed
field `k`, valued in a `k`-algebra field, takes values in the image of `k`. -/
private theorem exists_algHom_pi_of_isSepClosed
    {k L : Type*} [Field k] [Field L] [Algebra k L] [IsSepClosed k]
    {I : Type*} [Finite I] (A : I → Type*) [∀ i, Field (A i)] [∀ i, Algebra k (A i)]
    (hsep : ∀ i, Module.Finite k (A i) ∧ Algebra.IsSeparable k (A i))
    (g : (Π i, A i) →ₐ[k] L) :
    ∃ g' : (Π i, A i) →ₐ[k] k, ∀ a, algebraMap k L (g' a) = g a := by
  let _ := Fintype.ofFinite I
  have hmul (a : Π i, A i) (j : I) : a * Pi.single j 1 = Pi.single j (a j) := by
    ext m
    by_cases hm : m = j
    · subst hm; simp [Pi.single_eq_same]
    · simp [Pi.single_eq_of_ne hm]
  obtain ⟨j, hj⟩ : ∃ j : I, g (Pi.single j 1) = 1 := by
    have hidem : ∀ j, g (Pi.single j 1) * g (Pi.single j 1) = g (Pi.single j 1) := by
      intro j
      rw [← map_mul, hmul]
      simp
    have hsum : ∑ j, g (Pi.single j 1) = 1 := by
      rw [← map_sum]
      have hone : ∑ j : I, (Pi.single j 1 : Π i, A i) = 1 := by
        ext k
        rw [Finset.sum_apply, Finset.sum_eq_single k]
        · simp [Pi.single_eq_same]
        · intro b _ hb; rw [Pi.single_eq_of_ne (Ne.symm hb)]
        · intro h; exact absurd (Finset.mem_univ k) h
      rw [hone, map_one]
    by_contra hcon
    push Not at hcon
    have hall : ∀ j, g (Pi.single j 1) = 0 := by
      intro j
      have hz : g (Pi.single j 1) * (g (Pi.single j 1) - 1) = 0 := by
        ring_nf; linear_combination hidem j
      rcases mul_eq_zero.mp hz with h | h
      · exact h
      · exact absurd (by linear_combination h) (hcon j)
    rw [show (∑ j, g (Pi.single j 1)) = ∑ _j : I, (0 : L) from
      Finset.sum_congr rfl fun j _ ↦ hall j] at hsum
    simp at hsum
  have _ := (hsep j).left
  have _ := (hsep j).right
  have hbij : Function.Bijective (algebraMap k (A j)) :=
    ⟨(algebraMap k (A j)).injective, IsSepClosed.algebraMap_surjective k (A j)⟩
  let e : k ≃ₐ[k] A j := AlgEquiv.ofBijective (Algebra.ofId k (A j)) hbij
  refine ⟨e.symm.toAlgHom.comp (Pi.evalAlgHom k A j), fun a ↦ ?_⟩
  show algebraMap k L (e.symm (a j)) = g a
  have hfac : g a = g (Pi.single j (a j)) := by
    rw [← hmul, map_mul, hj, mul_one]
  rw [hfac]
  set r := e.symm (a j) with hr
  have hxj : a j = algebraMap k (A j) r := (e.apply_symm_apply (a j)).symm
  rw [hxj]
  have hsmul : (Pi.single j (algebraMap k (A j) r) : Π i, A i) = r • Pi.single j 1 := by
    rw [Algebra.smul_def, hmul]
    rfl
  rw [hsmul, map_smul, hj, Algebra.algebraMap_eq_smul_one r]

open scoped Classical in
/-- A point of an étale algebra over a separably closed field `k`, valued in a `k`-algebra
field, takes values in the image of `k`: such an algebra is a finite product of copies of `k`. -/
private theorem exists_algHom_of_isSepClosed {k L : Type*} [Field k] [Field L] [Algebra k L]
    [IsSepClosed k] (B : Type*) [CommRing B] [Algebra k B] [Algebra.Etale k B]
    (g : B →ₐ[k] L) :
    ∃ g' : B →ₐ[k] k, ∀ b, algebraMap k L (g' b) = g b := by
  obtain ⟨I, _, A, hfield, halg, e, hsep⟩ :=
    (Algebra.Etale.iff_exists_algEquiv_prod k B).mp inferInstance
  let _ := Fintype.ofFinite I
  let _ : ∀ i, Field (A i) := hfield
  let _ : ∀ i, Algebra k (A i) := halg
  obtain ⟨g', hg'⟩ := exists_algHom_pi_of_isSepClosed A hsep (g.comp e.symm.toAlgHom)
  exact ⟨g'.comp e.toAlgHom, fun b ↦ by simpa using hg' (e b)⟩

/-- An étale algebra point prescribed through a field extension of the residue field lifts
uniquely to the henselian local ring. This is
`HenselianLocalRing.existsUnique_algHom_residue_of_etale` after descending the prescribed point
to the residue field, which is separably closed. -/
private theorem existsUnique_algHom_of_etale
    {R A B L : Type u} [CommRing R] [CommRing A] [CommRing B] [Field L]
    [Algebra R A] [Algebra R B] [Algebra R L] [Algebra.Etale R A]
    [HenselianLocalRing B] [IsSepClosed (ResidueField B)]
    (δ : ResidueField B →ₐ[R] L) (ψ : A →ₐ[R] L) :
    ∃! f : A →ₐ[R] B, ∀ a, δ (residue B (f a)) = ψ a := by
  let _ : Algebra (ResidueField B) L := δ.toRingHom.toAlgebra
  let _ : IsScalarTower R (ResidueField B) L :=
    IsScalarTower.of_algebraMap_eq fun r ↦ (δ.commutes r).symm
  obtain ⟨g', hg'⟩ := exists_algHom_of_isSepClosed (k := ResidueField B) (ResidueField B ⊗[R] A)
    (Algebra.TensorProduct.lift (Algebra.ofId _ _) ψ fun _ _ ↦ mul_comm _ _)
  let ψ' : A →ₐ[R] ResidueField B :=
    (g'.restrictScalars R).comp Algebra.TensorProduct.includeRight
  have hψ' (a : A) : δ (ψ' a) = ψ a :=
    (hg' (1 ⊗ₜ[R] a)).trans <| by
      show algebraMap (ResidueField B) L 1 * ψ a = ψ a
      rw [map_one, one_mul]
  obtain ⟨f, hf, hu⟩ := HenselianLocalRing.existsUnique_algHom_residue_of_etale ψ'
  refine ⟨f, fun a ↦ by rw [hf, hψ'], fun f' hf' ↦
    hu f' fun a ↦ δ.injective ((hf' a).trans (hψ' a).symm)⟩

/-- **Stacks Project, Tag 08HR**, in the form the specialization-map construction needs: a point
of an ind-étale algebra prescribed through a field extension of the residue field of a henselian
local algebra lifts uniquely. The ind-étale algebra is a filtered colimit of étale ones, and the
lift is assembled from the unique lifts of the stages. -/
private theorem existsUnique_algHom_of_indEtale
    {R A B L : Type u} [CommRing R] [CommRing A] [CommRing B] [Field L]
    [Algebra R A] [Algebra R B] [Algebra R L]
    [HenselianLocalRing B] [IsSepClosed (ResidueField B)]
    (hind : (CommAlgCat.etale R).ind.{u} (CommAlgCat.of R A))
    (δ : ResidueField B →ₐ[R] L) (ψ : A →ₐ[R] L) :
    ∃! f : A →ₐ[R] B, ∀ a, δ (residue B (f a)) = ψ a := by
  classical
  obtain ⟨J, _, _, pres, het⟩ := hind
  have lift (j : J) := @existsUnique_algHom_of_etale R (pres.diag.obj j) B L
    _ _ _ _ _ _ _ (het j) _ _ δ (ψ.comp (pres.ι.app j).hom)
  choose fs hfs huniq using lift
  let c : Cocone pres.diag :=
    { pt := CommAlgCat.of R B
      ι :=
        { app := fun j ↦ CommAlgCat.ofHom (fs j)
          naturality := by
            intro i j m
            refine CommAlgCat.hom_ext (huniq i _ fun a ↦ ?_)
            show δ (residue B (fs j ((pres.diag.map m).hom a))) = ψ ((pres.ι.app i).hom a)
            rw [hfs j]
            exact congrArg ψ (ConcreteCategory.congr_hom (pres.w m) a) } }
  let f : A →ₐ[R] B := (pres.isColimit.desc c).hom
  let δ' : B →ₐ[R] L := δ.comp (IsScalarTower.toAlgHom R B (ResidueField B))
  have fac : CommAlgCat.ofHom (δ'.comp f) = CommAlgCat.ofHom ψ := by
    refine pres.isColimit.hom_ext fun j ↦ ?_
    show pres.ι.app j ≫ (pres.isColimit.desc c ≫ CommAlgCat.ofHom δ') = _
    rw [← Category.assoc, pres.isColimit.fac]
    ext a
    exact hfs j a
  refine ⟨f, fun a ↦ ConcreteCategory.congr_hom fac a, fun f' hf' ↦ ?_⟩
  refine CommAlgCat.hom_ext_iff.mp (pres.isColimit.hom_ext fun j ↦ ?_)
  show pres.ι.app j ≫ CommAlgCat.ofHom f' = pres.ι.app j ≫ pres.isColimit.desc c
  rw [pres.isColimit.fac]
  exact CommAlgCat.hom_ext (huniq j _ fun a ↦ hf' ((pres.ι.app j).hom a))

/-! ### Geometric fibres -/

/-- The fibre of a morphism of schemes over a geometric point of its target. -/
@[sga "1 IX 6.1", sga "3 XII 1.3" "more general", sga "4½ Th_finitude 2.11"]
abbrev fiberOverGeometricPoint (f : X ⟶ S) (s : GeometricPoint S) : Scheme.{u} :=
  pullback f s.hom

/-- The fibre of a geometrically connected morphism over a geometric point is connected. -/
instance connectedSpace_fiberOverGeometricPoint (f : X ⟶ S) [GeometricallyConnected f]
    (s : GeometricPoint S) : ConnectedSpace (fiberOverGeometricPoint f s) :=
  GeometricallyConnected.geometrically_connectedSpace _ _ _ (.of_hasPullback _ _)

/-- The map from the fibre over a geometric point into a base change through which the
geometric point factors. -/
def fiberOverGeometricPointMap (f : X ⟶ S) (s : GeometricPoint S) {T : Scheme.{u}} (g : T ⟶ S)
    (p : s.source ⟶ T) (hp : p ≫ g = s.hom) :
    fiberOverGeometricPoint f s ⟶ pullback f g :=
  pullback.lift (pullback.fst f s.hom) (pullback.snd f s.hom ≫ p) (by
    rw [Category.assoc, hp, pullback.condition])


/-- The map between base changes of `f` induced by a morphism of the two base schemes over
`S`. -/
def pullbackBaseChangeMap (f : X ⟶ S) {T U : Scheme.{u}} (g : T ⟶ S) (h : U ⟶ S)
    (c : T ⟶ U) (hc : c ≫ h = g) : pullback f g ⟶ pullback f h :=
  pullback.lift (pullback.fst f g) (pullback.snd f g ≫ c) (by
    rw [Category.assoc, hc, pullback.condition])

/-- Factoring a geometric point through `T` and then pushing to `U` gives the same map of
geometric fibres as factoring it through `U` directly. -/
theorem geometricFiberMap_comp_pullbackBaseChangeMap (f : X ⟶ S) (s : GeometricPoint S)
    {T U : Scheme.{u}} (g : T ⟶ S) (p : s.source ⟶ T) (hp : p ≫ g = s.hom)
    (h : U ⟶ S) (c : T ⟶ U) (hc : c ≫ h = g) :
    fiberOverGeometricPointMap f s g p hp ≫ pullbackBaseChangeMap f g h c hc
      = fiberOverGeometricPointMap f s h (p ≫ c) (by rw [Category.assoc, hc, hp]) := by
  apply pullback.hom_ext <;>
    rw [fiberOverGeometricPointMap, pullbackBaseChangeMap, fiberOverGeometricPointMap]
  · rw [Category.assoc, pullback.lift_fst, pullback.lift_fst, pullback.lift_fst]
  · rw [Category.assoc, pullback.lift_snd, pullback.lift_snd_assoc, pullback.lift_snd,
    Category.assoc]

/-- A morphism `Spec B ⟶ S` out of a henselian local ring with separably closed residue field
factors through an ind-étale algebra `A` over the stalk of `S` at a point `z` whose structure
morphism it dominates, compatibly with a given field point of both. This is the geometric form
of the functoriality of strict henselization used to compose specialization maps. -/
private theorem exists_comp_eq_of_indEtale {S : Scheme.{u}} (z : S) (A B K : Type u)
    [CommRing A] [CommRing B] [Field K] [Algebra (S.presheaf.stalk z) A]
    [HenselianLocalRing B] [IsSepClosed (ResidueField B)]
    (hind : (CommAlgCat.etale (S.presheaf.stalk z)).ind.{u}
      (CommAlgCat.of (S.presheaf.stalk z) A))
    (g : Spec (.of B) ⟶ S) (p : Spec (.of K) ⟶ Spec (.of B))
    (q : Spec (.of K) ⟶ Spec (.of A))
    (hp : p (closedPoint K) = closedPoint B)
    (hq : q ≫ Spec.map (CommRingCat.ofHom (algebraMap (S.presheaf.stalk z) A)) ≫
      S.fromSpecStalk z = p ≫ g) :
    ∃ c : Spec (.of B) ⟶ Spec (.of A),
      c ≫ Spec.map (CommRingCat.ofHom (algebraMap (S.presheaf.stalk z) A)) ≫
        S.fromSpecStalk z = g ∧ p ≫ c = q := by
  have hb : g (closedPoint B) ⤳ z := by
    show g (closedPoint B) ∈ {y : S | y ⤳ z}
    rw [← S.range_fromSpecStalk]
    refine ⟨(q ≫ Spec.map (CommRingCat.ofHom
      (algebraMap (S.presheaf.stalk z) A))) (closedPoint K), ?_⟩
    have he := congrArg (fun k : Spec (.of K) ⟶ S => k (closedPoint K)) hq
    change (S.fromSpecStalk z) ((Spec.map (CommRingCat.ofHom
      (algebraMap (S.presheaf.stalk z) A))) (q (closedPoint K))) = g (p (closedPoint K)) at he
    rwa [hp] at he
  let r : S.presheaf.stalk z ⟶ CommRingCat.of B :=
    S.presheaf.stalkSpecializes hb ≫ Scheme.stalkClosedPointTo g
  have hr : Spec.map r ≫ S.fromSpecStalk z = g := by
    dsimp only [r]
    rw [Spec.map_comp, Category.assoc, Scheme.SpecMap_stalkSpecializes_fromSpecStalk]
    exact Scheme.Spec_stalkClosedPointTo_fromSpecStalk g
  let _ : Algebra (S.presheaf.stalk z) B := r.hom.toAlgebra
  have hpR : IsLocalHom (Spec.preimage p).hom := by
    refine ((local_hom_TFAE (Spec.preimage p).hom).out 4 1).mp fun x hx ↦ ?_
    have h : (maximalIdeal K).comap (Spec.preimage p).hom = maximalIdeal B := by
      rw [← Spec.map_preimage p] at hp
      exact congrArg PrimeSpectrum.asIdeal hp
    rwa [← h] at hx
  let _ : Algebra (S.presheaf.stalk z) K := ((Spec.preimage p).hom.comp r.hom).toAlgebra
  let δ : ResidueField B →ₐ[S.presheaf.stalk z] K :=
    { __ := ResidueField.lift (Spec.preimage p).hom
      commutes' := fun x ↦ ResidueField.lift_residue_apply (Spec.preimage p).hom (r.hom x) }
  have hcomm : (Spec.preimage q).hom.comp (algebraMap (S.presheaf.stalk z) A)
      = (Spec.preimage p).hom.comp r.hom := by
    refine CommRingCat.hom_ext_iff.mp (Spec.map_injective ?_)
    show Spec.map (CommRingCat.ofHom (algebraMap (S.presheaf.stalk z) A) ≫ Spec.preimage q)
      = Spec.map (r ≫ Spec.preimage p)
    rw [Spec.map_comp, Spec.map_comp, Spec.map_preimage, Spec.map_preimage]
    refine (cancel_mono (S.fromSpecStalk z)).mp ?_
    simpa only [Category.assoc, hr] using hq
  let ψ : A →ₐ[S.presheaf.stalk z] K :=
    { __ := (Spec.preimage q).hom
      commutes' := fun x ↦ RingHom.congr_fun hcomm x }
  obtain ⟨c, hc, -⟩ := existsUnique_algHom_of_indEtale hind δ ψ
  refine ⟨Spec.map (CommRingCat.ofHom c.toRingHom), ?_, ?_⟩
  · rw [← Spec.map_comp_assoc]
    show Spec.map (CommRingCat.ofHom
      (c.toRingHom.comp (algebraMap (S.presheaf.stalk z) A))) ≫ S.fromSpecStalk z = g
    have he : c.toRingHom.comp (algebraMap (S.presheaf.stalk z) A) = r.hom := by
      ext x
      exact c.commutes x
    rwa [he]
  · rw [← Spec.map_preimage p, ← Spec.map_comp, ← Spec.map_preimage q]
    refine congrArg _ (CommRingCat.hom_ext ?_)
    ext x
    exact (ResidueField.lift_residue_apply (Spec.preimage p).hom (c x)).symm.trans (hc x)

/-! ### Specialization maps -/

/-- A continuous homomorphism `π₁(X_{s̄'}) → π₁(X_{s̄})` is a *specialization map* when it arises
from the strict henselization `A` of `𝒪_{S,s}` relative to a separable closure of `κ(s)`:
both geometric points factor through `Spec A`, the special one through its closed point, base
change along `X_{s̄} ⟶ X_A` is an equivalence on finite étale covers, and the homomorphism
satisfies the defining equation against the canonical maps. -/
@[sga "1 XIII 2.10" "special case"]
def IsSpecializationMap (f : X ⟶ S) [IsProper f] [GeometricallyConnected f]
    (s' s : GeometricPoint S)
    (x' : GeometricPoint (fiberOverGeometricPoint f s'))
    (x : GeometricPoint (fiberOverGeometricPoint f s))
    (sp : EtaleFundamentalGroup (fiberOverGeometricPoint f s') x' →ₜ*
      EtaleFundamentalGroup (fiberOverGeometricPoint f s) x) : Prop :=
  let z : S := s.hom (closedPoint s.residueField)
  let R := S.presheaf.stalk z
  ∃ (A : Type u) (hA : CommRing A) (hAloc : IsLocalRing A) (hAlg : Algebra R A),
    letI : CommRing A := hA
    letI : IsLocalRing A := hAloc
    letI : Algebra R A := hAlg
    Nonempty (Stacks.StrictHenselization.IsStrictHenselization R
      (SeparableClosure (maximalIdeal R).ResidueField) A) ∧
    let g : Spec (.of A) ⟶ S :=
      Spec.map (CommRingCat.ofHom (algebraMap R A)) ≫ S.fromSpecStalk z
    ∃ (p' : s'.source ⟶ Spec (.of A)) (hp' : p' ≫ g = s'.hom)
      (p : s.source ⟶ Spec (.of A)) (hp : p ≫ g = s.hom),
      p (closedPoint s.residueField) = closedPoint A ∧
      let i' : fiberOverGeometricPoint f s' ⟶ pullback f g :=
        fiberOverGeometricPointMap f s' g p' hp'
      let i : fiberOverGeometricPoint f s ⟶ pullback f g := fiberOverGeometricPointMap f s g p hp
      ∃ (hXA : ConnectedSpace (pullback f g : Scheme.{u}))
        (_hi : (finiteEtaleBaseChange i).IsEquivalence),
        letI : ConnectedSpace (pullback f g : Scheme.{u}) := hXA
        ∃ t : finiteEtaleFiberFunctor (x'.map i') ≅ finiteEtaleFiberFunctor (x.map i),
          ∀ γ, etaleFundamentalGroupMap i x (sp γ)
            = etaleFundamentalGroupMulEquiv t (etaleFundamentalGroupMap i' x' γ)

/-- Transport along the identity fibre-functor isomorphism is the identity. -/
theorem etaleFundamentalGroupMulEquiv_refl [ConnectedSpace X] {x : GeometricPoint X}
    (σ : EtaleFundamentalGroup X x) :
    etaleFundamentalGroupMulEquiv (Iso.refl (finiteEtaleFiberFunctor x)) σ = σ := by
  apply Aut.ext
  apply Iso.ext
  apply NatTrans.ext
  funext V
  rfl

/-- Transport along a fibre-functor isomorphism and back along its inverse is the identity. -/
theorem etaleFundamentalGroupMulEquiv_symm_apply_apply [ConnectedSpace X]
    {x y : GeometricPoint X}
    (t : finiteEtaleFiberFunctor x ≅ finiteEtaleFiberFunctor y)
    (σ : EtaleFundamentalGroup X x) :
    etaleFundamentalGroupMulEquiv t.symm (etaleFundamentalGroupMulEquiv t σ) = σ := by
  rw [← etaleFundamentalGroupMulEquiv_trans, t.self_symm_id,
    etaleFundamentalGroupMulEquiv_refl]

/-- Two consecutive defining equations for specialization maps compose to one, over the
composite morphism of base changes: the required fibre-functor isomorphism is assembled from
the transport of the first one and the second one. -/
private theorem exists_fiberFunctorIso_comp {Y₀ Y₁ Y₂ T₁ T₂ : Scheme.{u}}
    [ConnectedSpace Y₀] [ConnectedSpace Y₁] [ConnectedSpace Y₂]
    [ConnectedSpace T₁] [ConnectedSpace T₂]
    (a₀ : Y₀ ⟶ T₁) (a₁ : Y₁ ⟶ T₁) (b₀ : Y₀ ⟶ T₂) (b₁ : Y₁ ⟶ T₂) (b₂ : Y₂ ⟶ T₂)
    (c : T₁ ⟶ T₂) (hb₀ : a₀ ≫ c = b₀) (hb₁ : a₁ ≫ c = b₁)
    (x₀ : GeometricPoint Y₀) (x₁ : GeometricPoint Y₁) (x₂ : GeometricPoint Y₂)
    (h₁ : EtaleFundamentalGroup Y₀ x₀ →ₜ* EtaleFundamentalGroup Y₁ x₁)
    (h₂ : EtaleFundamentalGroup Y₁ x₁ →ₜ* EtaleFundamentalGroup Y₂ x₂)
    (t₁ : finiteEtaleFiberFunctor (x₀.map a₀) ≅ finiteEtaleFiberFunctor (x₁.map a₁))
    (t₂ : finiteEtaleFiberFunctor (x₁.map b₁) ≅ finiteEtaleFiberFunctor (x₂.map b₂))
    (hh₁ : ∀ σ, etaleFundamentalGroupMap a₁ x₁ (h₁ σ)
      = etaleFundamentalGroupMulEquiv t₁ (etaleFundamentalGroupMap a₀ x₀ σ))
    (hh₂ : ∀ σ, etaleFundamentalGroupMap b₂ x₂ (h₂ σ)
      = etaleFundamentalGroupMulEquiv t₂ (etaleFundamentalGroupMap b₁ x₁ σ)) :
    ∃ t : finiteEtaleFiberFunctor (x₀.map b₀) ≅ finiteEtaleFiberFunctor (x₂.map b₂),
      ∀ σ, etaleFundamentalGroupMap b₂ x₂ (h₂ (h₁ σ))
        = etaleFundamentalGroupMulEquiv t (etaleFundamentalGroupMap b₀ x₀ σ) := by
  subst hb₀
  subst hb₁
  refine ⟨fiberFunctorMapCompIso a₀ c x₀ ≪≫ fiberFunctorTransportIso c t₁ ≪≫
    (fiberFunctorMapCompIso a₁ c x₁).symm ≪≫ t₂, fun σ ↦ ?_⟩
  rw [etaleFundamentalGroupMulEquiv_trans, etaleFundamentalGroupMulEquiv_trans,
    etaleFundamentalGroupMulEquiv_trans, etaleFundamentalGroupMulEquiv_mapCompIso,
    etaleFundamentalGroupMulEquiv_transportIso, ← hh₁,
    ← etaleFundamentalGroupMulEquiv_mapCompIso,
    etaleFundamentalGroupMulEquiv_symm_apply_apply, hh₂]

/-- **Stacks Project, Tag 0C0L.** For a proper morphism with geometrically connected fibres and
specializations `s'' ⇝ s' ⇝ s`, the composite of a specialization map
`π₁(X_{s̄''}) → π₁(X_{s̄'})` with a specialization map `π₁(X_{s̄'}) → π₁(X_{s̄})` is again a
specialization map `π₁(X_{s̄''}) → π₁(X_{s̄})`. -/
@[stacks 0C0L]
theorem isSpecializationMap_comp (f : X ⟶ S) [IsProper f] [GeometricallyConnected f]
    (s'' s' s : GeometricPoint S)
    (x'' : GeometricPoint (fiberOverGeometricPoint f s''))
    (x' : GeometricPoint (fiberOverGeometricPoint f s'))
    (x : GeometricPoint (fiberOverGeometricPoint f s))
    (h₁ : EtaleFundamentalGroup (fiberOverGeometricPoint f s'') x'' →ₜ*
      EtaleFundamentalGroup (fiberOverGeometricPoint f s') x')
    (h₂ : EtaleFundamentalGroup (fiberOverGeometricPoint f s') x' →ₜ*
      EtaleFundamentalGroup (fiberOverGeometricPoint f s) x)
    (hs₁ : IsSpecializationMap f s'' s' x'' x' h₁)
    (hs₂ : IsSpecializationMap f s' s x' x h₂) :
    IsSpecializationMap f s'' s x'' x (h₂.comp h₁) := by
  simp only [IsSpecializationMap] at hs₁ hs₂ ⊢
  obtain ⟨A₁, hA₁, hLoc₁, hAlg₁, hSH₁, p₁', hp₁', p₁, hp₁, hclosed₁, hXA₁, hi₁, t₁,
    hform₁⟩ := hs₁
  obtain ⟨A₂, hA₂, hLoc₂, hAlg₂, hSH₂, p₂', hp₂', p₂, hp₂, hclosed₂, hXA₂, hi₂, t₂,
    hform₂⟩ := hs₂
  let _ : CommRing A₁ := hA₁
  let _ : IsLocalRing A₁ := hLoc₁
  let _ : Algebra (S.presheaf.stalk (s'.hom (closedPoint s'.residueField))) A₁ := hAlg₁
  let _ : CommRing A₂ := hA₂
  let _ : IsLocalRing A₂ := hLoc₂
  let _ : Algebra (S.presheaf.stalk (s.hom (closedPoint s.residueField))) A₂ := hAlg₂
  let _ : HenselianLocalRing A₁ := hSH₁.some.henselian
  let _ : IsSepClosed (ResidueField A₁) :=
    (have := hSH₁.some.sepClosed; isSepClosed_residueField_of_maximalIdeal A₁)
  obtain ⟨c, hc, hpc⟩ := exists_comp_eq_of_indEtale
    (s.hom (closedPoint s.residueField)) A₂ A₁ s'.residueField
    ((CommAlgCat.etale _).ind.prop_of_iso (CommAlgCat.isoMk (ULift.algEquiv))
      hSH₂.some.isFilteredColimitEtale)
    _ p₁ p₂' hclosed₁ (hp₂'.trans hp₁.symm)
  let g₁ : Spec (.of A₁) ⟶ S :=
    Spec.map (CommRingCat.ofHom
      (algebraMap (S.presheaf.stalk (s'.hom (closedPoint s'.residueField))) A₁)) ≫
      S.fromSpecStalk (s'.hom (closedPoint s'.residueField))
  let g₂ : Spec (.of A₂) ⟶ S :=
    Spec.map (CommRingCat.ofHom
      (algebraMap (S.presheaf.stalk (s.hom (closedPoint s.residueField))) A₂)) ≫
      S.fromSpecStalk (s.hom (closedPoint s.residueField))
  let _ : ConnectedSpace (pullback f g₁ : Scheme.{u}) := hXA₁
  let _ : ConnectedSpace (pullback f g₂ : Scheme.{u}) := hXA₂
  have hp₀ : (p₁' ≫ c) ≫ g₂ = s''.hom := by rw [Category.assoc, hc]; exact hp₁'
  have hd : fiberOverGeometricPointMap f s' g₁ p₁ hp₁ ≫ pullbackBaseChangeMap f g₁ g₂ c hc
      = fiberOverGeometricPointMap f s' g₂ p₂' hp₂' := by
    rw [geometricFiberMap_comp_pullbackBaseChangeMap]
    congr 1
  have hd₀ : fiberOverGeometricPointMap f s'' g₁ p₁' hp₁' ≫ pullbackBaseChangeMap f g₁ g₂ c hc
      = fiberOverGeometricPointMap f s'' g₂ (p₁' ≫ c) hp₀ :=
    geometricFiberMap_comp_pullbackBaseChangeMap f s'' g₁ p₁' hp₁' g₂ c hc
  obtain ⟨t, ht⟩ := exists_fiberFunctorIso_comp
    (fiberOverGeometricPointMap f s'' g₁ p₁' hp₁') (fiberOverGeometricPointMap f s' g₁ p₁ hp₁)
    (fiberOverGeometricPointMap f s'' g₂ (p₁' ≫ c) hp₀)
    (fiberOverGeometricPointMap f s' g₂ p₂' hp₂')
    (fiberOverGeometricPointMap f s g₂ p₂ hp₂) (pullbackBaseChangeMap f g₁ g₂ c hc) hd₀ hd
    x'' x' x h₁ h₂ t₁ t₂ hform₁ hform₂
  exact ⟨A₂, hA₂, hLoc₂, hAlg₂, hSH₂, p₁' ≫ c, hp₀, p₂, hp₂, hclosed₂, hXA₂, hi₂, t, ht⟩

end AlgebraicGeometry

end
