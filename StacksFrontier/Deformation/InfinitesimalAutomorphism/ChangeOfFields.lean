module

public import StacksFrontier.Algebra.Module.OppositeOfCommSemiring
public import StacksFrontier.Deformation.InfinitesimalAutomorphism.TangentVectorSpace
public import StacksFrontier.Deformation.LiftsOfObjects.AutomorphismFunctorRS
public import StacksFrontier.Deformation.TangentSpace.LinearFunctor
public import StacksFrontier.Deformation.VersalObject.ChangeOfFieldsConditionS2

/-!
# Infinitesimal automorphisms under a change of residue field (Stacks 07WC)

Let `Λ → k → l` be the standing finite tower of Tag 07W8 and let `𝓕` be a deformation
category over `𝒞_{Λ,k}`. The space of infinitesimal automorphisms of `𝓕`, namely the tangent
space at the identity of the automorphism functor of an object over the residue field, extends
by scalars along `k → l` to the corresponding space for the change-of-residue-field category:

`l ⊗_k Inf(𝓕) ≃ₗ[l] Inf(𝓕_{l/k})`.

Both sides are tangent spaces of automorphism functors, carrying the vector-space structures of
Tag 06JV. The automorphism functor of a chosen pushforward, read on the square-zero extensions
of the residue field, satisfies (RS) by Tag 06JU, hence sends the zero module to a singleton and
the two product projections to a bijection, and therefore has a linear lift. A linear functor on
finite-dimensional vector spaces is tensoring with its value on the ground field, so the
asserted equivalence compares that lift at the line `l` viewed over `k` with its value at `k`.
The comparison functor `B ↦ B ×_l k` carries the square-zero extension `l[l]` to `k[l]`, which
is what matches the two sides, and the change of residue field of a deformation category again
satisfies (RS) by Tag 07WA.

## Main results

* `Deformation.existsUnique_infinitesimalAutomorphismsChangeOfFields`: **Stacks 07WC**.

## Implementation notes

The scalar extension is produced directly, without passing through the tangent space of the
functor of fibrewise isomorphism classes: Tag 07WB is stated for that functor over
`𝒞_{Λ,l}`, whereas the automorphism functor of a point lives over `𝒞_{A,k}` for `A` the
residue-field object, so instantiating 07WB here would need a restriction functor
`𝒞_{l,l} ⥤ 𝒞_{k,l}` and the invariance of the tangent space under it. Neither is needed:
the comparison functor `B ↦ B ×_l k` already carries `l[l]` to `k[l]`, which is what matches
the two automorphism functors, and the scalar extension is then read off the linear lift of
Tag 06IA applied to the automorphism functor itself.

The equivalence is pinned by an existence-and-uniqueness statement rather than chosen as data.
Its characterizing property names a morphism `x₀ ⟶ x_{l,0}` of the chosen points over the two
residue fields and a comparison `h` of their pushforwards to the dual numbers whose base
morphism has prescribed pullback coordinates; conjugation by `h` then determines the image of
each pure tensor `1 ⊗ t`, and pure tensors generate. The tensor factors are written
`l ⊗_k Inf(𝓕)` so that the left `l`-module structure of the tensor product is the one the
equivalence carries.

## References

* [Stacks Project, Tag 07WC](https://stacks.math.columbia.edu/tag/07WC)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u v w y z x a u₁ uR mR vR

namespace Deformation

/-- The zero finite-dimensional vector space, in a universe independent of the field's. -/
private abbrev zeroFGModuleLifted (R : Type uR) [CommRing R] : FGModuleCat.{mR} R :=
  FGModuleCat.of R PUnit

/-- The product of two finite-dimensional vector spaces, in a universe independent of the
field's. -/
private abbrev prodFGModuleLifted (R : Type uR) [CommRing R] (M N : FGModuleCat.{mR} R) :
    FGModuleCat.{mR} R := FGModuleCat.of R (M × N)

/-- The first projection of a product of finite-dimensional vector spaces. -/
private abbrev prodFstLifted (R : Type uR) [CommRing R] (M N : FGModuleCat.{mR} R) :
    prodFGModuleLifted R M N ⟶ M := FGModuleCat.ofHom (LinearMap.fst R M N)

/-- The second projection of a product of finite-dimensional vector spaces. -/
private abbrev prodSndLifted (R : Type uR) [CommRing R] (M N : FGModuleCat.{mR} R) :
    prodFGModuleLifted R M N ⟶ N := FGModuleCat.ofHom (LinearMap.snd R M N)

/-- A functor on finite-dimensional vector spaces has its canonical linear lift when it sends
the zero space to a singleton and the two product projections to a bijection. -/
private noncomputable def linearFunctorLiftOfZeroAndProducts
    (R : Type uR) [CommRing R] (L : FGModuleCat.{mR} R ⥤ Type vR)
    (hzero : Nonempty (L.obj (zeroFGModuleLifted R)))
    (hsub : Subsingleton (L.obj (zeroFGModuleLifted R)))
    (hprod : ∀ M N, Function.Bijective
      (fun x : L.obj (prodFGModuleLifted R M N) ↦
        (L.map (prodFstLifted R M N) x, L.map (prodSndLifted R M N) x))) :
    LinearFunctorLift R L :=
  let prodIsLimit := fun M N : FGModuleCat.{mR} R ↦ Limits.BinaryFan.isLimitMk
    (fun s ↦ FGModuleCat.ofHom (LinearMap.prod s.fst.hom.hom s.snd.hom.hom))
    (fun _ ↦ by ext; rfl) (fun _ ↦ by ext; rfl)
    (fun _ f hf hg ↦ by
      ext x
      · exact congrArg (fun q ↦ q.hom.hom x) hf
      · exact congrArg (fun q ↦ q.hom.hom x) hg)
  letI : Unique (L.obj (zeroFGModuleLifted R)) :=
    { default := Classical.choice hzero, uniq := fun _ ↦ hsub.elim _ _ }
  letI : ∀ X : FGModuleCat.{mR} R, Nonempty (X ⟶ zeroFGModuleLifted R) :=
    fun _ ↦ ⟨FGModuleCat.ofHom 0⟩
  letI : ∀ X : FGModuleCat.{mR} R, Subsingleton (X ⟶ zeroFGModuleLifted R) :=
    fun _ ↦ ⟨fun _ _ ↦ by ext⟩
  letI : Limits.HasTerminal (FGModuleCat.{mR} R) :=
    Limits.hasTerminal_of_unique (zeroFGModuleLifted R)
  letI : ∀ M N : FGModuleCat.{mR} R, Limits.HasLimit (Limits.pair M N) :=
    fun M N ↦ ⟨⟨Limits.BinaryFan.mk (prodFstLifted R M N) (prodSndLifted R M N),
      prodIsLimit M N⟩⟩
  letI : Limits.HasBinaryProducts (FGModuleCat.{mR} R) :=
    Limits.hasBinaryProducts_of_hasLimit_pair _
  letI : Limits.HasFiniteProducts (FGModuleCat.{mR} R) :=
    CategoryTheory.hasFiniteProducts_of_has_binary_and_terminal
  letI : ∀ M N : FGModuleCat.{mR} R, Limits.PreservesLimit (Limits.pair M N) L :=
    fun M N ↦ Limits.preservesLimit_of_preserves_limit_cone (prodIsLimit M N)
      ((Limits.isLimitMapConeBinaryFanEquiv L (prodFstLifted R M N) (prodSndLifted R M N)).symm
        (let e := Equiv.ofBijective _ (hprod M N)
         Limits.BinaryFan.isLimitMk
          (fun s ↦ ↾fun x ↦ e.symm (s.fst x, s.snd x))
          (fun s ↦ by ext x; exact congrArg Prod.fst (e.apply_symm_apply (s.fst x, s.snd x)))
          (fun s ↦ by ext x; exact congrArg Prod.snd (e.apply_symm_apply (s.fst x, s.snd x)))
          (fun s f hf hg ↦ by
            ext x
            apply e.injective
            change e (f x) = e (e.symm (s.fst x, s.snd x))
            rw [e.apply_symm_apply]
            dsimp [e]
            apply Prod.ext
            · simpa using congrArg (fun q ↦ (ConcreteCategory.hom q) x) hf
            · simpa using congrArg (fun q ↦ (ConcreteCategory.hom q) x) hg)))
  letI : Limits.PreservesLimitsOfShape (Discrete Limits.WalkingPair) L :=
    { preservesLimit := by
        intro K
        exact Limits.preservesLimit_of_iso_diagram L (Limits.diagramIsoPair K).symm }
  letI : Limits.PreservesLimitsOfShape (Discrete PEmpty) L :=
    { preservesLimit := by
        intro K
        let c : Limits.Cone K := Limits.Cone.mk (zeroFGModuleLifted R)
          { app := fun j ↦ nomatch j.as
            naturality := fun X _ _ ↦ PEmpty.elim X.as }
        let hc : Limits.IsLimit c :=
          { lift := fun _ ↦ FGModuleCat.ofHom 0
            fac := fun _ j ↦ nomatch j.as
            uniq := fun _ _ _ ↦ Subsingleton.elim _ _ }
        apply Limits.preservesLimit_of_preserves_limit_cone hc
        letI : Unique (L.mapCone c).pt :=
          { default := (default : L.obj (zeroFGModuleLifted R))
            uniq := fun a ↦ hsub.elim a _ }
        exact (Limits.Types.isLimit_iff_bijective_sectionOfCone _).mpr
          ⟨fun _ _ _ ↦ Subsingleton.elim _ _,
            fun y ↦ ⟨default, Subsingleton.elim _ _⟩⟩ |>.some }
  letI : Limits.PreservesFiniteProducts L :=
    Limits.PreservesFiniteProducts.of_preserves_binary_and_terminal L
  fgModuleCatLinearFunctorLift R L

/-- Cancelling a pair of mutually inverse arrows conjugated by an isomorphism. -/
private lemma comp_cancel_iso_pair {C : Type u} [Category.{v} C] {X Y Z T : C}
    (q : X ⟶ Y) (i : Y ≅ Z) (g : Z ⟶ T) (g' : T ⟶ Z) (hg : g ≫ g' = 𝟙 Z) :
    (q ≫ i.hom ≫ g) ≫ g' ≫ i.inv = q := by
  rw [Category.assoc, Category.assoc, ← Category.assoc g g' i.inv, hg, Category.id_comp,
    Iso.hom_inv_id, Category.comp_id]

/-- Cancelling a pair of mutually inverse arrows on the other side of an isomorphism. -/
private lemma comp_cancel_iso_pair' {C : Type u} [Category.{v} C] {X Y Z T : C}
    (q : X ⟶ T) (i : Y ≅ Z) (g : Z ⟶ T) (g' : T ⟶ Z) (hg : g' ≫ g = 𝟙 T) :
    (q ≫ g' ≫ i.inv) ≫ i.hom ≫ g = q := by
  rw [Category.assoc, Category.assoc, ← Category.assoc i.inv i.hom g, Iso.inv_hom_id,
    Category.id_comp, hg, Category.comp_id]

private lemma unique_hom_of_specialFiber
    {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
    {F : Type y} [Category.{z} F]
    {p : F ⥤ Deformation.ArtinianLocalAlgCat.{u, max v w, w} Λ k}
    (hp : IsPredeformationCategory p)
    (X : p.Fiber (residueFieldObject.{u, v, w} Λ k))
    (Y : F) (e : p.obj Y ≅ residueFieldObject.{u, v, w} Λ k) :
    Nonempty (Unique (X.val ⟶ Y)) := by
  classical
  let L := cofiberedFiberLift p hp.cofibered e.hom ⟨Y, rfl⟩
  let φ : Y ⟶ L.1.val := L.2.val
  let : p.IsHomLift e.hom φ := L.2.property
  let : p.IsStronglyCocartesian e.hom φ :=
    isStronglyCocartesian_of_isCofiberedInGroupoids hp.cofibered e.hom φ L.2.property
  let : IsIso φ := Functor.IsStronglyCocartesian.isIso_of_base_isIso p e.hom φ
  let E := hp.specialFiber.some
  let m : X ⟶ L.1 := E.functor.preimage (eqToHom (Subsingleton.elim _ _))
  refine ⟨{ default := m.val ≫ inv φ, uniq := ?_ }⟩
  intro n
  have hn : p.IsHomLift (𝟙 (residueFieldObject.{u, v, w} Λ k)) (n ≫ φ) := by
    apply IsHomLift.of_fac' p _ _ X.property L.1.property
    have hm : eqToHom X.property.symm ≫ p.map (n ≫ φ) ≫ eqToHom L.1.property =
        𝟙 (residueFieldObject.{u, v, w} Λ k) := by
      ext a
      apply ULift.ext
      exact (residueFieldObject_residue Λ k _).symm.trans
        (((eqToHom X.property.symm ≫ p.map (n ≫ φ) ≫ eqToHom L.1.property).residue_comm a).trans
          (residueFieldObject_residue Λ k a))
    simpa using congrArg (fun f => eqToHom X.property ≫ f ≫ eqToHom L.1.property.symm) hm
  let m' : X ⟶ L.1 := ⟨n ≫ φ, hn⟩
  have hh : m' = m := E.functor.map_injective (Subsingleton.elim _ _)
  have h := congrArg (fun f : X ⟶ L.1 => f.val ≫ inv φ) hh
  simpa [m'] using h

private def residueFieldObjectULiftIso
    (Λ : Type u) (k : Type w) [CommRing Λ] [Field k] [Algebra Λ k] :
    residueFieldObject.{u, max v w, w} Λ k ≅
      residueFieldObject.{u, v, w} Λ k := by
  let e : ULift.{max v w} k ≃ₐ[Λ] ULift.{v} k :=
    (ULift.algEquiv (R := Λ) (A := k)).trans (ULift.algEquiv (R := Λ) (A := k)).symm
  let f : residueFieldObject.{u, max v w, w} Λ k ⟶
      residueFieldObject.{u, v, w} Λ k :=
    { hom := e.toAlgHom
      isLocal := IsLocalHom.of_surjective e.toAlgHom.toRingHom e.surjective
      residue_comm := by
        intro a
        rw [residueFieldObject_residue, residueFieldObject_residue]
        rfl }
  letI := Deformation.ArtinianLocalAlgCat.isIso_of_bijective_hom f e.bijective
  exact asIso f

private lemma unique_hom_changeOfFields_point
    (S : Deformation.ChangeOfFieldsSituation.{u, v, w})
    {F : Type y} [Category.{z} F]
    (p : F ⥤ Deformation.ArtinianLocalAlgCat.{u, max v w, v} S.Λ S.k)
    (hp : IsPredeformationCategory p)
    (x₀ : p.Fiber (residueFieldObject.{u, w, v} S.Λ S.k))
    (xₗ : (Deformation.changeOfFieldsProjection S p).Fiber
      (residueFieldObject.{u, v, w} S.Λ S.l)) :
    Nonempty (Unique (x₀.val ⟶ xₗ.val.fst)) := by
  let e := xₗ.val.iso ≪≫
    (Deformation.comparisonFunctor S).functor.mapIso (eqToIso xₗ.property) ≪≫
      comparisonResidueFieldIso.{u,v,w,v} S ≪≫
        residueFieldObjectULiftIso.{u,w,v} S.Λ S.k
  exact unique_hom_of_specialFiber hp x₀ xₗ.val.fst e


private lemma fiberAut_map_eq_id {C : Type u} [Category.{v} C]
    {F : Type y} [Category.{z} F] (p : F ⥤ C) {A : C}
    (x : p.Fiber A) (a : Aut x) : p.map a.asIso.hom.val = 𝟙 (p.obj x.val) := by
  let := a.asIso.hom.property
  have h := IsHomLift.fac' p (𝟙 A) a.asIso.hom.val
  simpa using h

private lemma pullbackAut_fst_map_eq_id
    {C : Type u} [Category.{v} C] {F : Type y} [Category.{z} F]
    {D : Type w} [Category.{x} D] (p : F ⥤ C) (G : D ⥤ C)
    {A : D} (X : (CategoricalPullback.π₂ p G).Fiber A) (a : Aut X) :
    p.map a.asIso.hom.val.fst = 𝟙 (p.obj X.val.fst) := by
  have hs : a.asIso.hom.val.snd = 𝟙 X.val.snd :=
    fiberAut_map_eq_id (CategoricalPullback.π₂ p G) X a
  have h := a.asIso.hom.val.w
  rw [hs, G.map_id, Category.comp_id] at h
  exact (cancel_mono X.val.iso.hom).mp (by simpa using h)

private lemma pullbackAut_fst_isHomLift
    {C : Type u} [Category.{v} C] {F : Type y} [Category.{z} F]
    {D : Type w} [Category.{x} D] (p : F ⥤ C) (G : D ⥤ C)
    {A : D} (X : (CategoricalPullback.π₂ p G).Fiber A) (a : Aut X) :
    p.IsHomLift (𝟙 (p.obj X.val.fst)) a.asIso.hom.val.fst := by
  rw [← pullbackAut_fst_map_eq_id p G X a]
  exact IsHomLift.map p _

private lemma pullbackAut_fst_injective
    {C : Type u} [Category.{v} C] {F : Type y} [Category.{z} F]
    {D : Type w} [Category.{x} D] (p : F ⥤ C) (G : D ⥤ C)
    {A : D} (X : (CategoricalPullback.π₂ p G).Fiber A) :
    Function.Injective (fun a : Aut X => a.asIso.hom.val.fst) := by
  intro a b hab
  apply Aut.ext
  apply Iso.ext
  apply Functor.Fiber.hom_ext
  apply CategoricalPullback.hom_ext hab
  exact (fiberAut_map_eq_id (CategoricalPullback.π₂ p G) X a).trans
    (fiberAut_map_eq_id (CategoricalPullback.π₂ p G) X b).symm


section

local instance infAutChangeOfFieldsModuleMulOpposite {k : Type w} [Field k]
    (V : FGModuleCat.{v} k) : Module kᵐᵒᵖ V :=
  Module.oppositeOfCommSemiring k V
local instance infAutChangeOfFieldsIsCentralScalar {k : Type w} [Field k]
    (V : FGModuleCat.{v} k) : IsCentralScalar k V :=
  Module.isCentralScalar_oppositeOfCommSemiring k V

private def squareZeroPairHom
    {R : Type u} [CommRing R]
    {M : Type v} [AddCommGroup M] [Module R M] [Module Rᵐᵒᵖ M] [IsCentralScalar R M]
    {N : Type w} [AddCommGroup N] [Module R N] [Module Rᵐᵒᵖ N] [IsCentralScalar R N]
    {A : Type a} [CommRing A]
    (f : A →+* TrivSqZeroExt R M) (g : A →+* TrivSqZeroExt R N)
    (h : ∀ a, (f a).fst = (g a).fst) : A →+* TrivSqZeroExt R (M × N) where
  toFun a := ⟨(f a).fst, ((f a).snd, (g a).snd)⟩
  map_one' := by simp; rfl
  map_mul' a b := by
    rw [f.map_mul, g.map_mul]
    apply TrivSqZeroExt.ext
    · rfl
    · apply Prod.ext
      · rfl
      · change (g a).fst • (g b).snd + MulOpposite.op (g b).fst • (g a).snd =
          (f a).fst • (g b).snd + MulOpposite.op (f b).fst • (g a).snd
        rw [h a, h b]
  map_zero' := by simp; rfl
  map_add' a b := by
    apply TrivSqZeroExt.ext
    · change (f (a + b)).fst = (f a).fst + (f b).fst
      rw [f.map_add]
      rfl
    · apply Prod.ext
      · change (f (a + b)).snd = (f a).snd + (f b).snd
        rw [f.map_add]
        rfl
      · change (g (a + b)).snd = (g a).snd + (g b).snd
        rw [g.map_add]
        rfl

/-- The zero map to the zero finite-dimensional vector space. -/
private abbrev squareZeroZeroMap {k : Type w} [Field k] (M : FGModuleCat.{max v w} k) :
    M ⟶ zeroFGModuleLifted k := FGModuleCat.ofHom 0

/-- The square whose two legs are the square-zero extensions of the product projections. -/
private noncomputable abbrev squareZeroProdCone {Λ : Type u} {k : Type w}
    [CommRing Λ] [Field k] [Algebra Λ k]
    (A : Deformation.ArtinianLocalAlgCat.{u, max v w, w} Λ k)
    (M N : FGModuleCat.{max v w} k) :
    PullbackCone ((squareZeroAlgFunctor A).map (squareZeroZeroMap M))
      ((squareZeroAlgFunctor A).map (squareZeroZeroMap N)) :=
  PullbackCone.mk ((squareZeroAlgFunctor A).map (prodFstLifted k M N))
    ((squareZeroAlgFunctor A).map (prodSndLifted k M N))
    (by
      rw [← (squareZeroAlgFunctor A).map_comp, ← (squareZeroAlgFunctor A).map_comp]
      congr 1)

private lemma squareZeroAlgFunctor_prod_isLimit {Λ : Type u} {k : Type w}
    [CommRing Λ] [Field k] [Algebra Λ k]
    (A : Deformation.ArtinianLocalAlgCat.{u, max v w, w} Λ k)
    (M N : FGModuleCat.{max v w} k) :
    Nonempty (IsLimit (squareZeroProdCone A M N)) := by
  let U := squareZeroAlgFunctor A
  let Z := zeroFGModuleLifted k
  let f : M ⟶ Z := squareZeroZeroMap M
  let g : N ⟶ Z := squareZeroZeroMap N
  refine ⟨PullbackCone.isLimitAux' _ ?_⟩
  intro s
  have he (a : s.pt.right) : (s.fst.right.hom a).fst = (s.snd.right.hom a).fst :=
    by
      have h := congrArg (fun h => (h.right.hom a).fst) s.condition
      change (((squareZeroAlgFunctor A).map f).right.hom (s.fst.right.hom a)).fst =
        (((squareZeroAlgFunctor A).map g).right.hom (s.snd.right.hom a)).fst at h
      exact (squareZeroAlgFunctor_map_fst A f _).symm.trans
        (h.trans (squareZeroAlgFunctor_map_fst A g _))
  let l : s.pt.right →ₐ[Λ] (U.obj (prodFGModuleLifted k M N)).right :=
    { squareZeroPairHom s.fst.right.hom.toRingHom s.snd.right.hom.toRingHom he with
      commutes' := by
        intro t
        apply TrivSqZeroExt.ext
        · change (s.fst.right.hom (algebraMap Λ s.pt.right t)).fst = _
          rw [s.fst.right.hom.commutes]; rfl
        · apply Prod.ext
          · change (s.fst.right.hom (algebraMap Λ s.pt.right t)).snd = _
            rw [s.fst.right.hom.commutes]; rfl
          · change (s.snd.right.hom (algebraMap Λ s.pt.right t)).snd = _
            rw [s.snd.right.hom.commutes]; rfl }
  let m : s.pt.right ⟶ (U.obj (prodFGModuleLifted k M N)).right :=
    { hom := l
      isLocal := ⟨fun a ha => by
        apply s.fst.right.isLocal.map_nonunit a
        apply TrivSqZeroExt.isUnit_iff_isUnit_fst.mpr
        have ht := TrivSqZeroExt.isUnit_iff_isUnit_fst.mp ha
        exact ht⟩
      residue_comm := fun a => s.fst.right.residue_comm a }
  let h : s.pt ⟶ U.obj (prodFGModuleLifted k M N) := Under.homMk m (by
    ext a
    apply TrivSqZeroExt.ext
    · exact congrArg (fun h => (h.hom a).fst) s.fst.w
    · exact Prod.ext (congrArg (fun h => (h.hom a).snd) s.fst.w)
        (congrArg (fun h => (h.hom a).snd) s.snd.w))
  refine ⟨h, ?_, ?_, ?_⟩
  · apply Under.UnderMorphism.ext
    ext a
    apply TrivSqZeroExt.ext
    · exact squareZeroAlgFunctor_map_fst A _ _
    · exact squareZeroAlgFunctor_map_snd A _ _
  · apply Under.UnderMorphism.ext
    ext a
    apply TrivSqZeroExt.ext
    · exact (squareZeroAlgFunctor_map_fst A _ _).trans (he a)
    · exact squareZeroAlgFunctor_map_snd A _ _
  · intro j hj₁ hj₂
    apply Under.UnderMorphism.ext
    ext a
    apply TrivSqZeroExt.ext
    · have hh := congrArg (fun q => (q.right.hom a).fst) hj₁
      change (((squareZeroAlgFunctor A).map _).right.hom (j.right.hom a)).fst = _ at hh
      exact (squareZeroAlgFunctor_map_fst A _ _).symm.trans hh
    · apply Prod.ext
      · have hh := congrArg (fun q => (q.right.hom a).snd) hj₁
        change (((squareZeroAlgFunctor A).map _).right.hom (j.right.hom a)).snd = _ at hh
        exact (squareZeroAlgFunctor_map_snd A _ _).symm.trans hh
      · have hh := congrArg (fun q => (q.right.hom a).snd) hj₂
        change (((squareZeroAlgFunctor A).map _).right.hom (j.right.hom a)).snd = _ at hh
        exact (squareZeroAlgFunctor_map_snd A _ _).symm.trans hh

/-- Automorphisms of a chosen pushforward are trivial when its structure morphism to the residue
field is bijective. -/
private lemma subsingleton_aut_of_bijective_residue
    {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
    {F : Type y} [Category.{z} F]
    {p : F ⥤ Deformation.ArtinianLocalAlgCat.{u, max v w, w} Λ k}
    (hp : IsPredeformationCategory p)
    (x₀ : p.Fiber (residueFieldObject.{u, v, w} Λ k))
    (P : ChosenPushforwardsAt p x₀.val) (U : Under (p.obj x₀.val))
    (hr : Function.Bijective (residueMorphism.{u, v, w} U.right).hom) :
    Subsingleton (Aut (P.obj U)) := by
  let := Deformation.ArtinianLocalAlgCat.isIso_of_bijective_hom _ hr
  let e := eqToIso (P.obj U).property ≪≫ asIso (residueMorphism.{u, v, w} U.right)
  let : Unique (x₀.val ⟶ (P.obj U).val) :=
    (unique_hom_of_specialFiber hp x₀ (P.obj U).val e).some
  refine ⟨fun a b => ?_⟩
  apply Aut.ext
  apply Iso.ext
  apply Functor.Fiber.hom_ext
  have hval : a.asIso.hom.val = b.asIso.hom.val := by
    let := P.inclusion_cocartesian U
    let : p.IsHomLift (𝟙 U.right) a.asIso.hom.val := a.asIso.hom.property
    let : p.IsHomLift (𝟙 U.right) b.asIso.hom.val := b.asIso.hom.property
    apply Functor.IsStronglyCocartesian.ext p U.hom (P.inclusion U) (𝟙 U.right)
    exact Subsingleton.elim _ _
  exact hval

private lemma automorphismFunctor_squareZero_zero_subsingleton
    {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
    {F : Type y} [Category.{z} F]
    {p : F ⥤ Deformation.ArtinianLocalAlgCat.{u, max v w, w} Λ k}
    (hp : IsPredeformationCategory p)
    (x₀ : p.Fiber (residueFieldObject.{u, v, w} Λ k))
    (P : ChosenPushforwardsAt p x₀.val) :
    Subsingleton (Aut (P.obj ((squareZeroAlgFunctor (p.obj x₀.val)).obj
      (zeroFGModuleLifted k)))) := by
  refine subsingleton_aut_of_bijective_residue hp x₀ P _ ⟨fun a b hab => ?_, fun a => ?_⟩
  · apply TrivSqZeroExt.ext
    · exact congrArg ULift.down hab
    · exact Subsingleton.elim _ _
  · exact ⟨⟨a.down, 0⟩, rfl⟩

private noncomputable def automorphismFunctor_squareZero_linearLift
    {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
    {F : Type y} [Category.{z} F]
    {p : F ⥤ Deformation.ArtinianLocalAlgCat.{u, max v w, w} Λ k}
    (hp : Deformation.IsDeformationCategory p)
    (x₀ : p.Fiber (residueFieldObject.{u, v, w} Λ k))
    (P : ChosenPushforwardsAt p x₀.val) :
    LinearFunctorLift k
      (squareZeroAlgFunctor.{u, v, w} (p.obj x₀.val) ⋙ Deformation.automorphismFunctor P) := by
  let U := squareZeroAlgFunctor.{u, v, w} (p.obj x₀.val)
  let H := U ⋙ Deformation.automorphismFunctor P
  let Z : FGModuleCat.{max v w} k := zeroFGModuleLifted.{w, max v w} k
  let hZ : Subsingleton (Aut (P.obj (U.obj Z))) :=
    automorphismFunctor_squareZero_zero_subsingleton.{u, v, w, y, z} hp.predeformation x₀ P
  refine linearFunctorLiftOfZeroAndProducts.{w, max v w, z} k H
    (show Nonempty (Aut (P.obj (U.obj Z))) from ⟨1⟩)
    (show Subsingleton (Aut (P.obj (U.obj Z))) from hZ) ?_
  intro M N
  let f : M ⟶ Z := squareZeroZeroMap.{v, w} M
  let g : N ⟶ Z := squareZeroZeroMap.{v, w} N
  have hc := squareZeroAlgFunctor_prod_isLimit.{u, v, w} (p.obj x₀.val) M N
  have hg : Function.Surjective (U.map g).right.hom := by
    intro a
    refine ⟨⟨a.fst, 0⟩, ?_⟩
    apply TrivSqZeroExt.ext
    · exact squareZeroAlgFunctor_map_fst.{u, v, w} (p.obj x₀.val) g _
    · exact Subsingleton.elim _ _
  let h := (Deformation.automorphismFunctor_satisfiesRS hp.satisfiesRS x₀.val P
    (U.map f) (U.map g) hg (squareZeroProdCone.{u, v, w} (p.obj x₀.val) M N) hc).some
  constructor
  · intro a b hab
    exact PullbackCone.IsLimit.type_ext h (congrArg Prod.fst hab) (congrArg Prod.snd hab)
  · rintro ⟨a, b⟩
    let : Subsingleton ((Deformation.automorphismFunctor P).obj (U.obj Z)) := hZ
    let t : Types.PullbackObj ((Deformation.automorphismFunctor P).map (U.map f))
        ((Deformation.automorphismFunctor P).map (U.map g)) :=
      ⟨⟨a, b⟩, Subsingleton.elim _ _⟩
    refine ⟨(PullbackCone.IsLimit.equivPullbackObj h).symm t, ?_⟩
    exact Prod.ext (PullbackCone.IsLimit.equivPullbackObj_symm_apply_fst h t)
      (PullbackCone.IsLimit.equivPullbackObj_symm_apply_snd h t)

end

private def tensorFromUnitLifted (K : Type w) [Field K] (V : FGModuleCat.{max v w} K) :
    V →ₗ[K] (FGModuleCat.of K (ULift.{v} K) ⟶ V) where
  toFun v := FGModuleCat.ofHom ((LinearMap.toSpanSingleton K V v).comp
    ULift.moduleEquiv.toLinearMap)
  map_add' x y := by
    apply FGModuleCat.hom_ext
    ext r
    exact smul_add r.down x y
  map_smul' r x := by
    apply FGModuleCat.hom_ext
    ext a
    exact smul_comm a.down r x

/-- Addition of morphisms in `FGModuleCat` acts pointwise on vectors. -/
private lemma fg_add_applyLifted {K : Type w} [Field K] {V W : FGModuleCat.{max v w} K}
    (f g : V ⟶ W) (x : V) : (f + g).hom x = f.hom x + g.hom x := by
  change (((forget₂ (FGModuleCat.{max v w} K) (ModuleCat.{max v w} K)).map (f + g)).hom) x = _
  rfl

/-- The canonical tensor map induced by the linear functor and a rank-one map. -/
private def tensorComparisonLifted
    (K : Type w) [Field K]
    (L : FGModuleCat.{max v w} K ⥤ ModuleCat.{u₁} K) [L.Additive] [L.Linear K]
    (T : Type u₁) [AddCommGroup T] [Module K T]
    (e : (L.obj (FGModuleCat.of K (ULift.{v} K)) : Type u₁) ≃ₗ[K] T)
    (V : FGModuleCat.{max v w} K) :
    TensorProduct K T V →ₗ[K] (L.obj V : Type u₁) :=
    TensorProduct.lift <| LinearMap.mk₂ K
    (fun x v ↦ (L.map (tensorFromUnitLifted K V v)).hom (e.symm x))
    (fun x y v ↦ by
      rw [e.symm.map_add]
      exact map_add _ _ _)
    (fun r x v ↦ by
      change (L.map (tensorFromUnitLifted K V v)).hom (e.symm (r • x)) = _
      rw [e.symm.map_smul]
      exact map_smul _ _ _)
    (fun x v₁ v₂ ↦ by
      rw [map_add, L.map_add]
      rfl)
    (fun r x v ↦ by
      change (L.map (tensorFromUnitLifted K V (r • v))).hom (e.symm x) = _
      rw [map_smul, L.map_smul]
      rfl)

/-- The basis-coordinate inverse to `tensorComparisonLifted`. -/
private noncomputable def tensorComparisonInvLifted
    (K : Type w) [Field K]
    (L : FGModuleCat.{max v w} K ⥤ ModuleCat.{u₁} K) [L.Additive] [L.Linear K]
    (T : Type u₁) [AddCommGroup T] [Module K T]
    (e : (L.obj (FGModuleCat.of K (ULift.{v} K)) : Type u₁) ≃ₗ[K] T)
    (V : FGModuleCat.{max v w} K) :
    (L.obj V : Type u₁) →ₗ[K] TensorProduct K T V := by
  let b := Module.finBasis K V
  exact
    { toFun := fun y ↦ ∑ i, e ((L.map (FGModuleCat.ofHom
          (ULift.moduleEquiv.symm.toLinearMap.comp (b.coord i)))).hom y) ⊗ₜ[K] b i
      map_add' := fun x y ↦ by simp [TensorProduct.add_tmul, Finset.sum_add_distrib]
      map_smul' := fun r x ↦ by
        simp [TensorProduct.smul_tmul, Finset.smul_sum] }

/-- `tensorComparisonLifted` followed by its basis-coordinate inverse is the identity. -/
private theorem tensorComparisonInv_compLifted
    (K : Type w) [Field K]
    (L : FGModuleCat.{max v w} K ⥤ ModuleCat.{u₁} K) [L.Additive] [L.Linear K]
    (T : Type u₁) [AddCommGroup T] [Module K T]
    (e : (L.obj (FGModuleCat.of K (ULift.{v} K)) : Type u₁) ≃ₗ[K] T)
    (V : FGModuleCat.{max v w} K) :
    tensorComparisonLifted K L T e V ∘ₗ tensorComparisonInvLifted K L T e V = LinearMap.id := by
  let b := Module.finBasis K V
  apply LinearMap.ext
  intro y
  simp only [LinearMap.comp_apply, LinearMap.id_apply]
  dsimp [tensorComparisonInvLifted]
  rw [map_sum]
  simp only [tensorComparisonLifted]
  change (∑ i, (L.map (tensorFromUnitLifted K V (b i))).hom
    (e.symm (e ((L.map (FGModuleCat.ofHom
      (ULift.moduleEquiv.symm.toLinearMap.comp (b.coord i)))).hom y)))) = y
  simp only [e.symm_apply_apply]
  have heq (i) : (L.map (tensorFromUnitLifted K V (b i))).hom
      ((L.map (FGModuleCat.ofHom (ULift.moduleEquiv.symm.toLinearMap.comp (b.coord i)))).hom y) =
      (L.map ((FGModuleCat.ofHom (ULift.moduleEquiv.symm.toLinearMap.comp (b.coord i)) :
          V ⟶ FGModuleCat.of K (ULift.{v} K)) ≫
        tensorFromUnitLifted K V (b i))).hom y := by
    rw [← ModuleCat.comp_apply, ← L.map_comp]
  simp_rw [heq]
  have h : (∑ i, (FGModuleCat.ofHom (ULift.moduleEquiv.symm.toLinearMap.comp (b.coord i)) :
      V ⟶ FGModuleCat.of K (ULift.{v} K)) ≫
      tensorFromUnitLifted K V (b i)) = 𝟙 V := by
    apply FGModuleCat.hom_ext
    ext v
    have eval_sum (s : Finset (Fin (Module.finrank K V))) :
        ModuleCat.Hom.hom (∑ i ∈ s,
          (FGModuleCat.ofHom (ULift.moduleEquiv.symm.toLinearMap.comp (b.coord i)) :
              V ⟶ FGModuleCat.of K (ULift.{v} K)) ≫
            tensorFromUnitLifted K V (b i)).hom v = ∑ i ∈ s, b.repr v i • b i := by
      classical
      induction s using Finset.induction with
      | empty => simp
      | @insert i s hi ih =>
          rw [Finset.sum_insert hi, Finset.sum_insert hi, fg_add_applyLifted, ih]
          have hterm : ((FGModuleCat.ofHom
                (ULift.moduleEquiv.symm.toLinearMap.comp (b.coord i)) :
              V ⟶ FGModuleCat.of K (ULift.{v} K)) ≫
              tensorFromUnitLifted K V (b i)).hom v = b.repr v i • b i := by
            change b.coord i v • b i = b.repr v i • b i
            rfl
          rw [hterm]
    rw [eval_sum Finset.univ, b.sum_repr]
    rfl
  calc
    _ = (L.map (∑ i, (FGModuleCat.ofHom
          (ULift.moduleEquiv.symm.toLinearMap.comp (b.coord i)) :
            V ⟶ FGModuleCat.of K (ULift.{v} K)) ≫
        tensorFromUnitLifted K V (b i))).hom y := by
          rw [L.map_sum]
          simp only [ModuleCat.hom_sum, LinearMap.sum_apply]
    _ = y := by rw [h, L.map_id]; rfl

/-- The basis-coordinate inverse followed by `tensorComparisonLifted` is the identity. -/
private theorem tensorComparison_compLifted
    (K : Type w) [Field K]
    (L : FGModuleCat.{max v w} K ⥤ ModuleCat.{u₁} K) [L.Additive] [L.Linear K]
    (T : Type u₁) [AddCommGroup T] [Module K T]
    (e : (L.obj (FGModuleCat.of K (ULift.{v} K)) : Type u₁) ≃ₗ[K] T)
    (V : FGModuleCat.{max v w} K) :
    tensorComparisonInvLifted K L T e V ∘ₗ tensorComparisonLifted K L T e V = LinearMap.id := by
  let b := Module.finBasis K V
  apply LinearMap.ext
  intro z
  induction z using TensorProduct.inductionOn with
  | tmul x v =>
      change (∑ i, e ((L.map (FGModuleCat.ofHom
          (ULift.moduleEquiv.symm.toLinearMap.comp (b.coord i)))).hom
        ((L.map (tensorFromUnitLifted K V v)).hom (e.symm x))) ⊗ₜ[K] b i) = x ⊗ₜ[K] v
      have h (i) : tensorFromUnitLifted K V v ≫
            FGModuleCat.ofHom (ULift.moduleEquiv.symm.toLinearMap.comp (b.coord i)) =
          (b.repr v i) • 𝟙 (FGModuleCat.of K (ULift.{v} K)) := by
        apply FGModuleCat.hom_ext
        apply LinearMap.ext
        intro r
        apply ULift.ext
        change b.coord i (r.down • v) = b.repr v i * r.down
        simp [b.coord_apply, mul_comm]
      have heq (i) : e ((L.map (FGModuleCat.ofHom
            (ULift.moduleEquiv.symm.toLinearMap.comp (b.coord i)))).hom
          ((L.map (tensorFromUnitLifted K V v)).hom (e.symm x))) = b.repr v i • x := by
        rw [← ModuleCat.comp_apply, ← L.map_comp, h, L.map_smul, L.map_id]
        simp
      simp_rw [heq, TensorProduct.smul_tmul]
      rw [← TensorProduct.tmul_sum, b.sum_repr]
  | add x y hx hy =>
      simpa only [map_add] using congrArg₂ (fun a b ↦ a + b) hx hy

/-- A linear functor on finite-dimensional vector spaces is tensoring with its
value at the rank-one module, with independent source and target universes. -/
private noncomputable def tensorComparisonLinearEquivLifted
    (K : Type w) [Field K]
    (L : FGModuleCat.{max v w} K ⥤ ModuleCat.{u₁} K) [L.Additive] [L.Linear K]
    (T : Type u₁) [AddCommGroup T] [Module K T]
    (e : (L.obj (FGModuleCat.of K (ULift.{v} K)) : Type u₁) ≃ₗ[K] T)
    (V : FGModuleCat.{max v w} K) :
    TensorProduct K T V ≃ₗ[K] (L.obj V : Type u₁) :=
  LinearEquiv.ofBijective (tensorComparisonLifted K L T e V) (by
    constructor
    · intro x y hxy
      have h := congrArg (tensorComparisonInvLifted K L T e V) hxy
      simpa only [← LinearMap.comp_apply, tensorComparison_compLifted,
        LinearMap.id_apply] using h
    · intro y
      refine ⟨tensorComparisonInvLifted K L T e V y, ?_⟩
      have h := congrArg (fun f : (L.obj V : Type u₁) →ₗ[K] (L.obj V : Type u₁) => f y)
        (tensorComparisonInv_compLifted K L T e V)
      simpa only [LinearMap.comp_apply, LinearMap.id_apply] using h)



private noncomputable def localizedTangentEquivAut
    {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
    {F : Type y} [Category.{z} F]
    {p : F ⥤ Deformation.ArtinianLocalAlgCat.{u, max v w, w} Λ k}
    (hp : IsPredeformationCategory p)
    (x₀ : p.Fiber (residueFieldObject.{u, v, w} Λ k))
    (P : ChosenPushforwardsAt p x₀.val) :
    localizedAutomorphismFunctorTangent P ≃
      Aut (P.obj (dualNumbersUnder (p := p) (x := x₀.val))) := by
  letI := residueAlgebra (p.obj x₀.val)
  let U := specialFibreUnder (p := p) (x := x₀.val)
  let r := residueMorphism.{u, v, w} U.right
  have hr (a : U.right) : r.hom a = ULift.up a.down := by
    apply ULift.ext
    change (residueFieldObject.{max v w, v, w} (p.obj x₀.val) k).residueEquiv
      (IsLocalRing.residue _ a) = a.down
    exact residueFieldObject_residue (p.obj x₀.val) k a
  have hb : Function.Bijective r.hom := by
    constructor
    · intro a b hab
      apply ULift.ext
      exact congrArg ULift.down ((hr a).symm.trans (hab.trans (hr b)))
    · intro a
      exact ⟨⟨a.down⟩, hr _⟩
  have hs := subsingleton_aut_of_bijective_residue hp x₀ P U hb
  refine (localizedTangentEquivKernel P).trans
    { toFun := Subtype.val
      invFun := fun a => ⟨a, ?_⟩
      left_inv := fun a => Subtype.ext rfl
      right_inv := fun _ => rfl }
  exact hs.elim _ _

private lemma localizedTangentEquivAut_add
    {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
    {F : Type y} [Category.{z} F]
    {p : F ⥤ Deformation.ArtinianLocalAlgCat.{u, max v w, w} Λ k}
    (hp : Deformation.IsDeformationCategory p)
    (x₀ : p.Fiber (residueFieldObject.{u, v, w} Λ k))
    (P : ChosenPushforwardsAt p x₀.val) :
    letI := naturalLocalizedTangentAddCommGroup P hp.satisfiesRS
    ∀ a b, localizedTangentEquivAut hp.predeformation x₀ P (a + b) =
      localizedTangentEquivAut hp.predeformation x₀ P a *
        localizedTangentEquivAut hp.predeformation x₀ P b := by
  intro a b
  exact congrArg Subtype.val ((naturalLocalizedTangentModule_spec P hp.satisfiesRS).1 a b)

private lemma localizedTangentEquivAut_smul
    {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
    {F : Type y} [Category.{z} F]
    {p : F ⥤ Deformation.ArtinianLocalAlgCat.{u, max v w, w} Λ k}
    (hp : Deformation.IsDeformationCategory p)
    (x₀ : p.Fiber (residueFieldObject.{u, v, w} Λ k))
    (P : ChosenPushforwardsAt p x₀.val) :
    letI := naturalLocalizedTangentAddCommGroup P hp.satisfiesRS
    letI := naturalLocalizedTangentModule P hp.satisfiesRS
    ∀ (c : k) a, localizedTangentEquivAut hp.predeformation x₀ P (c • a) =
      P.transportAutHom (tangentScaling c)
        (localizedTangentEquivAut hp.predeformation x₀ P a) := by
  intro c a
  exact (naturalLocalizedTangentModule_spec P hp.satisfiesRS).2 c a

section

local instance infAutLocalizedTangentModuleMulOpposite {k : Type w} [Field k]
    (V : FGModuleCat.{v} k) : Module kᵐᵒᵖ V :=
  Module.oppositeOfCommSemiring k V
local instance infAutLocalizedTangentIsCentralScalar {k : Type w} [Field k]
    (V : FGModuleCat.{v} k) : IsCentralScalar k V :=
  Module.isCentralScalar_oppositeOfCommSemiring k V

attribute [local implicit_reducible] algebrasUnder squareZeroExtensionArtinian
  Deformation.changeOfFieldsProjection Functor.Fiber.fiberInclusion CategoricalPullback.π₂
  Functor.Fiber

private lemma typesEqToHom_apply {A B : Type z} (h : A = B) (a : A) :
    (eqToHom h) a = cast h a := by cases h; rfl

private def linearLiftEquiv {R : Type u} [CommRing R]
    {C : Type v} [Category.{w} C] [Preadditive C] [Linear R C]
    {H : C ⥤ Type z} (L : LinearFunctorLift R H) (X : C) :
    (L.functor.obj X : Type z) ≃ H.obj X :=
  Equiv.cast (congrArg (fun F : C ⥤ Type z => F.obj X) L.forget_comp)

private lemma linearLiftEquiv_map {R : Type u} [CommRing R]
    {C : Type v} [Category.{w} C] [Preadditive C] [Linear R C]
    {H : C ⥤ Type z} (L : LinearFunctorLift R H)
    {X Y : C} (f : X ⟶ Y) (a : L.functor.obj X) :
    linearLiftEquiv L Y (L.functor.map f a) = H.map f (linearLiftEquiv L X a) := by
  have h := ConcreteCategory.congr_hom ((eqToHom L.forget_comp).naturality f) a
  change (eqToHom L.forget_comp).app Y (L.functor.map f a) =
    H.map f ((eqToHom L.forget_comp).app X a) at h
  simp only [eqToHom_app, typesEqToHom_apply] at h
  exact h

private lemma linearLiftEquiv_zero {R : Type u} [CommRing R]
    {C : Type v} [Category.{w} C] [Preadditive C] [Linear R C]
    {H : C ⥤ Type z} [∀ X, Group (H.obj X)]
    (L : LinearFunctorLift R H)
    (hone : ∀ {X Y} (f : X ⟶ Y), H.map f 1 = 1) (X : C) :
    linearLiftEquiv L X 0 = 1 := by
  have h := linearLiftEquiv_map L (0 : X ⟶ X) ((linearLiftEquiv L X).symm 1)
  simpa only [L.functor.map_zero, ModuleCat.hom_zero, LinearMap.zero_apply,
    Equiv.apply_symm_apply, hone] using h

private lemma linearLiftEquiv_add {R : Type u} [CommRing R]
    {H : FGModuleCat.{v} R ⥤ Type z} [∀ X, Group (H.obj X)]
    (L : LinearFunctorLift R H)
    (hone : ∀ {X Y} (f : X ⟶ Y), H.map f 1 = 1)
    (hmul : ∀ {X Y} (f : X ⟶ Y) a b, H.map f (a * b) = H.map f a * H.map f b)
    (X : FGModuleCat.{v} R) (a b : L.functor.obj X) :
    linearLiftEquiv L X (a + b) = linearLiftEquiv L X a * linearLiftEquiv L X b := by
  let Z := prodFGModuleLifted R X X
  let f : Z ⟶ X := prodFstLifted R X X
  let g : Z ⟶ X := prodSndLifted R X X
  let i : X ⟶ Z := FGModuleCat.ofHom (LinearMap.inl R X X)
  let j : X ⟶ Z := FGModuleCat.ofHom (LinearMap.inr R X X)
  have hif : i ≫ f = 𝟙 X := by ext; rfl
  have hig : i ≫ g = 0 := by ext; rfl
  have hjf : j ≫ f = 0 := by ext; rfl
  have hjg : j ≫ g = 𝟙 X := by ext; rfl
  let c := (linearLiftEquiv L Z).symm
    (linearLiftEquiv L Z (L.functor.map i a) * linearLiftEquiv L Z (L.functor.map j b))
  have hc (r : Z ⟶ X) :
      linearLiftEquiv L X (L.functor.map r c) =
        linearLiftEquiv L X (L.functor.map (i ≫ r) a) *
        linearLiftEquiv L X (L.functor.map (j ≫ r) b) := by
    rw [linearLiftEquiv_map, Equiv.apply_symm_apply, hmul]
    simp only [← linearLiftEquiv_map, L.functor.map_comp, ModuleCat.comp_apply]
  have hf : L.functor.map f c = a := by
    apply (linearLiftEquiv L X).injective
    simpa only [hif, hjf, L.functor.map_id, L.functor.map_zero,
      ModuleCat.id_apply, ModuleCat.hom_zero, LinearMap.zero_apply,
      linearLiftEquiv_zero L hone, mul_one] using hc f
  have hg : L.functor.map g c = b := by
    apply (linearLiftEquiv L X).injective
    simpa only [hig, hjg, L.functor.map_id, L.functor.map_zero,
      ModuleCat.id_apply, ModuleCat.hom_zero, LinearMap.zero_apply,
      linearLiftEquiv_zero L hone, one_mul] using hc g
  have hh : i ≫ (f + g) = 𝟙 X := by rw [Preadditive.comp_add, hif, hig, add_zero]
  have hk : j ≫ (f + g) = 𝟙 X := by rw [Preadditive.comp_add, hjf, hjg, zero_add]
  have h := hc (f + g)
  simpa only [hh, hk, L.functor.map_add, L.functor.map_id,
    ModuleCat.hom_add, LinearMap.add_apply, ModuleCat.id_apply, hf, hg] using h

private lemma linearLiftEquiv_smul {R : Type u} [CommRing R]
    {C : Type v} [Category.{w} C] [Preadditive C] [Linear R C]
    {H : C ⥤ Type z} (L : LinearFunctorLift R H)
    (X : C) (r : R) (a : L.functor.obj X) :
    linearLiftEquiv L X (r • a) = H.map (r • 𝟙 X) (linearLiftEquiv L X a) := by
  simpa only [L.functor.map_smul, L.functor.map_id, ModuleCat.hom_smul,
    ModuleCat.hom_id, LinearMap.smul_apply, LinearMap.id_apply] using
      linearLiftEquiv_map L (r • 𝟙 X) a

private lemma squareZeroAlgFunctor_algebraMap
    {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
    (A : Deformation.ArtinianLocalAlgCat.{u, max v w, w} Λ k)
    (M : FGModuleCat.{max v w} k) (a : Λ) :
    algebraMap Λ ((squareZeroAlgFunctor A).obj M).right a =
      TrivSqZeroExt.inl (algebraMap Λ k a) := by
  change TrivSqZeroExt.inl (A.residueEquiv
    (IsLocalRing.residue A (algebraMap Λ A a))) = _
  congr 1
  exact A.residueEquiv.commutes a

private noncomputable def comparisonSquareZeroEquiv
    (S : Deformation.ChangeOfFieldsSituation.{u, v, w})
    (A : Deformation.ArtinianLocalAlgCat.{u, max v w, v} S.Λ S.k)
    (B : Deformation.ArtinianLocalAlgCat.{u, max v w, w} S.Λ S.l) :
    ((squareZeroAlgFunctor A).obj (FGModuleCat.of S.k (ULift.{v} S.l))).right ≃ₐ[S.Λ]
      (Deformation.comparisonFunctor S).functor.obj
        ((squareZeroAlgFunctor B).obj (FGModuleCat.of S.l (ULift.{v} S.l))).right := by
  let V := ((squareZeroAlgFunctor B).obj (FGModuleCat.of S.l (ULift.{v} S.l))).right
  let e := (Deformation.comparisonFunctor S).pullbackEquiv V
  let f : ((squareZeroAlgFunctor A).obj (FGModuleCat.of S.k (ULift.{v} S.l))).right ≃+*
      RingHom.pullback (residueMap S V) (algebraMap S.k S.l) :=
    { toFun := fun a => ⟨(⟨algebraMap S.k S.l a.fst, a.snd⟩, a.fst), rfl⟩
      invFun := fun b => ⟨b.val.2, b.val.1.snd⟩
      left_inv := fun a => rfl
      right_inv := fun b => by
        apply Subtype.ext
        apply Prod.ext
        · apply TrivSqZeroExt.ext
          · exact b.property.symm
          · rfl
        · rfl
      map_mul' := by
        intro a b
        apply Subtype.ext
        apply Prod.ext
        · apply TrivSqZeroExt.ext
          · exact map_mul _ _ _
          · apply ULift.ext
            change a.fst • b.snd.down + b.fst • a.snd.down =
              algebraMap S.k S.l a.fst * b.snd.down +
                algebraMap S.k S.l b.fst * a.snd.down
            simp only [Algebra.smul_def]
        · rfl
      map_add' := by
        intro a b
        apply Subtype.ext
        apply Prod.ext
        · apply TrivSqZeroExt.ext
          · exact map_add _ _ _
          · rfl
        · rfl }
  apply AlgEquiv.ofRingEquiv (f := f.trans e.symm)
  intro a
  apply e.injective
  change e (e.symm (f (algebraMap S.Λ _ a))) = e (algebraMap S.Λ _ a)
  rw [e.apply_symm_apply]
  apply Subtype.ext
  apply Prod.ext
  · rw [(Deformation.comparisonFunctor S).algebraMap_fst]
    rw [squareZeroAlgFunctor_algebraMap, squareZeroAlgFunctor_algebraMap]
    apply TrivSqZeroExt.ext
    · exact (IsScalarTower.algebraMap_apply S.Λ S.k S.l a).symm
    · rfl
  · rw [(Deformation.comparisonFunctor S).algebraMap_snd]
    rw [squareZeroAlgFunctor_algebraMap]
    rfl

private lemma comparisonSquareZeroEquiv_coordinates
    (S : Deformation.ChangeOfFieldsSituation.{u, v, w})
    (A : Deformation.ArtinianLocalAlgCat.{u, max v w, v} S.Λ S.k)
    (B : Deformation.ArtinianLocalAlgCat.{u, max v w, w} S.Λ S.l)
    (a : ((squareZeroAlgFunctor A).obj (FGModuleCat.of S.k (ULift.{v} S.l))).right) :
    ((Deformation.comparisonFunctor S).pullbackEquiv
      ((squareZeroAlgFunctor B).obj (FGModuleCat.of S.l (ULift.{v} S.l))).right
        (comparisonSquareZeroEquiv S A B a)).val =
      (⟨algebraMap S.k S.l a.fst, a.snd⟩, a.fst) := by
  simp only [comparisonSquareZeroEquiv, AlgEquiv.ofRingEquiv_apply,
    RingEquiv.trans_apply, RingEquiv.apply_symm_apply]
  rfl

private noncomputable def comparisonSquareZeroIso
    (S : Deformation.ChangeOfFieldsSituation.{u, v, w})
    (A : Deformation.ArtinianLocalAlgCat.{u, max v w, v} S.Λ S.k)
    (B : Deformation.ArtinianLocalAlgCat.{u, max v w, w} S.Λ S.l) :
    ((squareZeroAlgFunctor A).obj (FGModuleCat.of S.k (ULift.{v} S.l))).right ≅
      (Deformation.comparisonFunctor S).functor.obj
        ((squareZeroAlgFunctor B).obj (FGModuleCat.of S.l (ULift.{v} S.l))).right := by
  let e := comparisonSquareZeroEquiv S A B
  let f : ((squareZeroAlgFunctor A).obj (FGModuleCat.of S.k (ULift.{v} S.l))).right ⟶
      (Deformation.comparisonFunctor S).functor.obj
        ((squareZeroAlgFunctor B).obj (FGModuleCat.of S.l (ULift.{v} S.l))).right :=
    { hom := e.toAlgHom
      isLocal := IsLocalHom.of_surjective _ e.surjective
      residue_comm := fun a => by
        rw [(Deformation.comparisonFunctor S).residue_snd]
        exact congrArg Prod.snd (comparisonSquareZeroEquiv_coordinates S A B a) }
  letI := Deformation.ArtinianLocalAlgCat.isIso_of_bijective_hom f e.bijective
  exact asIso f

private def fiberAutConjugate {C : Type u} [Category.{v} C]
    {F : Type y} [Category.{z} F] (p : F ⥤ C) {A B : C}
    (X : p.Fiber A) (Y : p.Fiber B) (e : X.val ≅ Y.val) (a : Aut X) : Aut Y := by
  let b := e.symm ≪≫ (Functor.Fiber.fiberInclusion.mapIso a.asIso) ≪≫ e
  have hv (a : Aut X) : p.IsHomLift (𝟙 B) (e.inv ≫ a.asIso.hom.val ≫ e.hom) := by
    apply IsHomLift.of_fac' p _ _ Y.property Y.property
    simp only [p.map_comp, fiberAut_map_eq_id, Category.id_comp,
      ← p.map_comp, e.inv_hom_id, p.map_id, Category.id_comp]
    simp
  exact .of
    { hom := ⟨b.hom, hv a⟩
      inv := ⟨b.inv, by
        simpa only [b, Iso.trans_inv, Iso.symm_inv, Iso.symm_hom, Functor.mapIso_inv, Aut.inv_asIso,
          Functor.Fiber.fiberInclusion, Category.assoc] using hv a⁻¹⟩
      hom_inv_id := by apply Functor.Fiber.hom_ext; exact b.hom_inv_id
      inv_hom_id := by apply Functor.Fiber.hom_ext; exact b.inv_hom_id }

private def fiberAutConjugateEquiv {C : Type u} [Category.{v} C]
    {F : Type y} [Category.{z} F] (p : F ⥤ C) {A B : C}
    (X : p.Fiber A) (Y : p.Fiber B) (e : X.val ≅ Y.val) : Aut X ≃* Aut Y where
  toFun := fiberAutConjugate p X Y e
  invFun := fiberAutConjugate p Y X e.symm
  left_inv a := by
    apply Aut.ext; apply Iso.ext; apply Functor.Fiber.hom_ext
    change e.hom ≫ (e.inv ≫ a.asIso.hom.val ≫ e.hom) ≫ e.inv = a.asIso.hom.val
    simp
  right_inv a := by
    apply Aut.ext; apply Iso.ext; apply Functor.Fiber.hom_ext
    change e.inv ≫ (e.hom ≫ a.asIso.hom.val ≫ e.inv) ≫ e.hom = a.asIso.hom.val
    simp
  map_mul' a b := by
    apply Aut.ext; apply Iso.ext; apply Functor.Fiber.hom_ext
    change e.inv ≫ (b.asIso.hom.val ≫ a.asIso.hom.val) ≫ e.hom =
      (e.inv ≫ b.asIso.hom.val ≫ e.hom) ≫ (e.inv ≫ a.asIso.hom.val ≫ e.hom)
    simp

private lemma fiberAutConjugateEquiv_comm {C : Type u} [Category.{v} C]
    {F : Type y} [Category.{z} F] (p : F ⥤ C) {A B : C}
    (X : p.Fiber A) (Y : p.Fiber B) (e : X.val ≅ Y.val) (a : Aut X) :
    a.asIso.hom.val ≫ e.hom = e.hom ≫ (fiberAutConjugateEquiv p X Y e a).asIso.hom.val := by
  change a.asIso.hom.val ≫ e.hom = e.hom ≫ e.inv ≫ a.asIso.hom.val ≫ e.hom
  simp

private def pullbackFiberAut
    {C : Type u} [Category.{v} C] {F : Type y} [Category.{z} F]
    {D : Type w} [Category.{x} D] (p : F ⥤ C) (G : D ⥤ C)
    {A : D} (X : (CategoricalPullback.π₂ p G).Fiber A)
    (a : Aut (Functor.Fiber.mk (p := p) (a := X.val.fst) rfl)) : Aut X := by
  let f (a : Aut (Functor.Fiber.mk (p := p) (a := X.val.fst) rfl)) :
      X.val ⟶ X.val :=
    { fst := a.asIso.hom.val
      snd := 𝟙 _
      w := by
        have hid : (p.map a.asIso.hom.val : p.obj X.val.fst ⟶ p.obj X.val.fst) =
            𝟙 (p.obj X.val.fst) := fiberAut_map_eq_id p _ a
        have hw : (p.map a.asIso.hom.val : p.obj X.val.fst ⟶ p.obj X.val.fst) ≫ X.val.iso.hom =
            X.val.iso.hom ≫ G.map (𝟙 X.val.snd) := by
          rw [hid, G.map_id, Category.id_comp, Category.comp_id]
        exact hw }
  have hf (a : Aut (Functor.Fiber.mk (p := p) (a := X.val.fst) rfl)) :
      (CategoricalPullback.π₂ p G).IsHomLift (𝟙 A) (f a) := by
    apply IsHomLift.of_fac' _ _ _ X.property X.property
    simp [f, CategoricalPullback.π₂]
  exact .of
    { hom := ⟨f a, hf a⟩
      inv := ⟨f a⁻¹, hf a⁻¹⟩
      hom_inv_id := by
        apply Functor.Fiber.hom_ext
        apply CategoricalPullback.hom_ext
        · exact congrArg Subtype.val a.asIso.hom_inv_id
        · change (𝟙 X.val.snd) ≫ 𝟙 X.val.snd = 𝟙 X.val.snd
          simp
      inv_hom_id := by
        apply Functor.Fiber.hom_ext
        apply CategoricalPullback.hom_ext
        · exact congrArg Subtype.val a.asIso.inv_hom_id
        · change (𝟙 X.val.snd) ≫ 𝟙 X.val.snd = 𝟙 X.val.snd
          simp }

private def pullbackFiberAutEquiv
    {C : Type u} [Category.{v} C] {F : Type y} [Category.{z} F]
    {D : Type w} [Category.{x} D] (p : F ⥤ C) (G : D ⥤ C)
    {A : D} (X : (CategoricalPullback.π₂ p G).Fiber A) :
    Aut (Functor.Fiber.mk (p := p) (a := X.val.fst) rfl) ≃* Aut X where
  toFun := pullbackFiberAut p G X
  invFun a := .of
    { hom := ⟨a.asIso.hom.val.fst, pullbackAut_fst_isHomLift p G X a⟩
      inv := ⟨a.asIso.inv.val.fst, pullbackAut_fst_isHomLift p G X a⁻¹⟩
      hom_inv_id := by
        apply Functor.Fiber.hom_ext
        exact congrArg (fun f => f.val.fst) a.asIso.hom_inv_id
      inv_hom_id := by
        apply Functor.Fiber.hom_ext
        exact congrArg (fun f => f.val.fst) a.asIso.inv_hom_id }
  left_inv a := by apply Aut.ext; apply Iso.ext; apply Functor.Fiber.hom_ext; rfl
  right_inv a := pullbackAut_fst_injective p G X rfl
  map_mul' a b := pullbackAut_fst_injective p G X rfl

private noncomputable def comparisonPushforward
    (S : Deformation.ChangeOfFieldsSituation.{u, v, w})
    {F : Type y} [Category.{z} F]
    (p : F ⥤ Deformation.ArtinianLocalAlgCat.{u, max v w, v} S.Λ S.k)
    (hp : Deformation.IsCofiberedInGroupoids p)
    {x₀ : F} (P : ChosenPushforwardsAt p x₀)
    {xₗ : ChangeOfFieldsCategory S p}
    (Q : ChosenPushforwardsAt (Deformation.changeOfFieldsProjection S p) xₗ)
    (j : x₀ ⟶ xₗ.fst) :
    let W := (squareZeroAlgFunctor (p.obj x₀)).obj (FGModuleCat.of S.k (ULift.{v} S.l))
    let V := (squareZeroAlgFunctor xₗ.snd).obj (FGModuleCat.of S.l (ULift.{v} S.l))
    { H : (P.obj W).val ≅ (Q.obj V).val.fst //
      P.inclusion W ≫ H.hom = j ≫ (Q.inclusion V).fst ∧
      eqToHom (P.obj W).property.symm ≫ p.map H.hom ≫
        (Q.obj V).val.iso.hom ≫
          (Deformation.comparisonFunctor S).functor.map (eqToHom (Q.obj V).property) =
        (comparisonSquareZeroIso S (p.obj x₀) xₗ.snd).hom } := by
  let G := (Deformation.comparisonFunctor S).functor
  let W := (squareZeroAlgFunctor (p.obj x₀)).obj (FGModuleCat.of S.k (ULift.{v} S.l))
  let V := (squareZeroAlgFunctor xₗ.snd).obj (FGModuleCat.of S.l (ULift.{v} S.l))
  let e := comparisonSquareZeroIso S (p.obj x₀) xₗ.snd
  let d := e ≪≫ G.mapIso (eqToIso (Q.obj V).property.symm) ≪≫ (Q.obj V).val.iso.symm
  letI := Q.inclusion_cocartesian V
  have hQ : (Q.inclusion V).snd ≫ eqToHom (Q.obj V).property = V.hom := by
    have h := IsHomLift.fac' (Deformation.changeOfFieldsProjection S p) V.hom (Q.inclusion V)
    have hh := congrArg (fun f => f ≫ eqToHom (Q.obj V).property) h
    simp only [Category.assoc, eqToHom_trans, eqToHom_refl, Category.comp_id,
      Category.id_comp] at hh
    exact hh
  have hf : W.hom ≫ e.hom = p.map (j ≫ (Q.inclusion V).fst) ≫
      (Q.obj V).val.iso.hom ≫ G.map (eqToHom (Q.obj V).property) := by
    rw [p.map_comp, Category.assoc, ← Category.assoc (p.map (Q.inclusion V).fst),
      (Q.inclusion V).w, Category.assoc, ← G.map_comp, hQ]
    apply Deformation.ArtinianLocalAlgCat.hom_ext
    apply AlgHom.ext
    intro a
    apply ((Deformation.comparisonFunctor S).pullbackEquiv V.right).injective
    have hd : ((Deformation.comparisonFunctor S).pullbackEquiv xₗ.snd
        (xₗ.iso.hom.hom ((p.map j).hom a))).val.2 =
        (p.obj x₀).residueEquiv (IsLocalRing.residue _ a) := by
      rw [← (Deformation.comparisonFunctor S).residue_snd]
      exact (xₗ.iso.hom.residue_comm _).trans ((p.map j).residue_comm a)
    apply Subtype.ext
    change ((Deformation.comparisonFunctor S).pullbackEquiv V.right
      (comparisonSquareZeroEquiv S (p.obj x₀) xₗ.snd (W.hom.hom a))).val = _
    rw [comparisonSquareZeroEquiv_coordinates]
    apply Prod.ext
    · refine Eq.trans ?_ ((Deformation.comparisonFunctor S).map_fst _ _).symm
      apply TrivSqZeroExt.ext
      · change algebraMap S.k S.l ((p.obj x₀).residueEquiv (IsLocalRing.residue _ a)) =
          residueMap S xₗ.snd
            (((Deformation.comparisonFunctor S).pullbackEquiv xₗ.snd
              (xₗ.iso.hom.hom ((p.map j).hom a))).val.1)
        rw [← hd]
        exact (((Deformation.comparisonFunctor S).pullbackEquiv xₗ.snd
          (xₗ.iso.hom.hom ((p.map j).hom a))).property).symm
      · rfl
    · refine Eq.trans ?_ ((Deformation.comparisonFunctor S).map_snd _ _).symm
      exact hd.symm
  have hcancel : G.map (eqToHom (Q.obj V).property) ≫
      G.map (eqToHom (Q.obj V).property.symm) = 𝟙 (G.obj (Q.obj V).val.snd) := by
    rw [← G.map_comp, eqToHom_trans, eqToHom_refl, G.map_id]
    exact rfl
  have hbase : W.hom ≫ d.hom = p.map (j ≫ (Q.inclusion V).fst) := by
    have hgoal : W.hom ≫ e.hom ≫ G.map (eqToHom (Q.obj V).property.symm) ≫
        (Q.obj V).val.iso.inv = p.map (j ≫ (Q.inclusion V).fst) := by
      rw [← Category.assoc W.hom e.hom, hf]
      exact comp_cancel_iso_pair _ _ _ _ hcancel
    exact hgoal
  letI := P.inclusion_cocartesian W
  letI : p.IsHomLift (W.hom ≫ d.hom) (j ≫ (Q.inclusion V).fst) := by
    rw [hbase]; infer_instance
  let h := Functor.IsStronglyCocartesian.map p W.hom (P.inclusion W) (g := d.hom)
    rfl (j ≫ (Q.inclusion V).fst)
  letI hlift : p.IsHomLift d.hom h := inferInstance
  letI hcart : p.IsStronglyCocartesian d.hom h :=
    isStronglyCocartesian_of_isCofiberedInGroupoids hp d.hom h hlift
  letI hdiso : IsIso d.hom := d.isIso_hom
  have hIso : IsIso h :=
    @Functor.IsStronglyCocartesian.isIso_of_base_isIso _ _ _ _ p _ _ _ _ d.hom h hcart hdiso
  refine ⟨@asIso _ _ _ _ h hIso, Functor.IsStronglyCocartesian.fac p W.hom (P.inclusion W)
    (g := d.hom) rfl (j ≫ (Q.inclusion V).fst), ?_⟩
  have hh := IsHomLift.fac' p d.hom h
  have hm : eqToHom (P.obj W).property.symm ≫ p.map h = d.hom := by
    have hh' := congrArg (fun f => eqToHom (P.obj W).property.symm ≫ f) hh
    simpa using hh'
  have hcancel' : G.map (eqToHom (Q.obj V).property.symm) ≫
      G.map (eqToHom (Q.obj V).property) = 𝟙 (G.obj V.right) := by
    rw [← G.map_comp, eqToHom_trans, eqToHom_refl, G.map_id]
  have hfinal : eqToHom (P.obj W).property.symm ≫ p.map h ≫
      (Q.obj V).val.iso.hom ≫ G.map (eqToHom (Q.obj V).property) = e.hom :=
    (Category.assoc (eqToHom (P.obj W).property.symm) (p.map h) _).symm.trans
      ((congrArg (fun m => m ≫ (Q.obj V).val.iso.hom ≫
          G.map (eqToHom (Q.obj V).property)) hm).trans
        (comp_cancel_iso_pair' e.hom (Q.obj V).val.iso
          (G.map (eqToHom (Q.obj V).property))
          (G.map (eqToHom (Q.obj V).property.symm)) hcancel'))
  exact hfinal

/-- Transport of automorphisms along a reindexed family of chosen pushforwards
sends the identity automorphism to the identity automorphism. -/
private lemma comp_automorphismFunctor_map_one {C : Type u} [Category.{v} C]
    {F : Type y} [Category.{z} F] {p : F ⥤ C} {X : F}
    {E : Type a} [Category.{u₁} E] (T : E ⥤ Under (p.obj X))
    (P : ChosenPushforwardsAt p X) {M N : E} (f : M ⟶ N) :
    letI : ∀ M : E, Group ((T ⋙ Deformation.automorphismFunctor P).obj M) :=
      fun M => inferInstanceAs (Group (Aut (P.obj (T.obj M))))
    (T ⋙ Deformation.automorphismFunctor P).map f 1 = 1 :=
  (P.transportAutHom (T.map f)).map_one

/-- Transport of automorphisms along a reindexed family of chosen pushforwards
is multiplicative. -/
private lemma comp_automorphismFunctor_map_mul {C : Type u} [Category.{v} C]
    {F : Type y} [Category.{z} F] {p : F ⥤ C} {X : F}
    {E : Type a} [Category.{u₁} E] (T : E ⥤ Under (p.obj X))
    (P : ChosenPushforwardsAt p X) {M N : E} (f : M ⟶ N) :
    letI : ∀ M : E, Group ((T ⋙ Deformation.automorphismFunctor P).obj M) :=
      fun M => inferInstanceAs (Group (Aut (P.obj (T.obj M))))
    ∀ c d, (T ⋙ Deformation.automorphismFunctor P).map f (c * d) =
      (T ⋙ Deformation.automorphismFunctor P).map f c *
        (T ⋙ Deformation.automorphismFunctor P).map f d :=
  fun c d => (P.transportAutHom (T.map f)).map_mul c d

/-- Scaling the dual-number coordinate of the square-zero extension of the
residue field transports automorphisms along the canonical tangent scaling. -/
private lemma comp_automorphismFunctor_map_smul_id {Λ : Type u} {k : Type w}
    [CommRing Λ] [Field k] [Algebra Λ k] {F : Type y} [Category.{z} F]
    {p : F ⥤ Deformation.ArtinianLocalAlgCat.{u, max v w, w} Λ k} {X : F}
    (P : ChosenPushforwardsAt p X) (r : k)
    (c : Aut (P.obj ((squareZeroAlgFunctor (p.obj X)).obj
      (FGModuleCat.of k (ULift.{v} k))))) :
    (squareZeroAlgFunctor (p.obj X) ⋙ Deformation.automorphismFunctor P).map
        (r • 𝟙 (FGModuleCat.of k (ULift.{v} k))) c =
      P.transportAutHom (tangentScaling (p := p) (x := X) r) c := rfl

/-- Under a linear lift of an automorphism functor, the canonical identification
with the underlying set-valued functor turns addition into composition. -/
private lemma linearLiftEquiv_transport_add {Λ : Type u} {k : Type w}
    [CommRing Λ] [Field k] [Algebra Λ k] {F : Type y} [Category.{z} F]
    {p : F ⥤ Deformation.ArtinianLocalAlgCat.{u, max v w, w} Λ k} {X : F}
    (T : FGModuleCat.{max v w} k ⥤ Under (p.obj X))
    (P : ChosenPushforwardsAt p X)
    (L : LinearFunctorLift k (T ⋙ Deformation.automorphismFunctor P))
    (M : FGModuleCat.{max v w} k) (a b : L.functor.obj M) :
    letI : ∀ N : FGModuleCat.{max v w} k,
        Group ((T ⋙ Deformation.automorphismFunctor P).obj N) :=
      fun N => inferInstanceAs (Group (Aut (P.obj (T.obj N))))
    linearLiftEquiv L M (a + b) = linearLiftEquiv L M a * linearLiftEquiv L M b :=
  letI : ∀ N : FGModuleCat.{max v w} k,
      Group ((T ⋙ Deformation.automorphismFunctor P).obj N) :=
    fun N => inferInstanceAs (Group (Aut (P.obj (T.obj N))))
  linearLiftEquiv_add L (comp_automorphismFunctor_map_one T P)
    (comp_automorphismFunctor_map_mul T P) M a b

private noncomputable def linearLiftTangentEquiv
    {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
    {F : Type y} [Category.{z} F]
    {p : F ⥤ Deformation.ArtinianLocalAlgCat.{u, max v w, w} Λ k}
    (hp : Deformation.IsDeformationCategory p)
    (x₀ : p.Fiber (residueFieldObject.{u, v, w} Λ k))
    (P : ChosenPushforwardsAt p x₀.val)
    (L : LinearFunctorLift k
      (squareZeroAlgFunctor (p.obj x₀.val) ⋙ Deformation.automorphismFunctor P)) :
    letI := naturalLocalizedTangentAddCommGroup P hp.satisfiesRS
    letI := naturalLocalizedTangentModule P hp.satisfiesRS
    (L.functor.obj (FGModuleCat.of k (ULift.{v} k)) : Type z) ≃ₗ[k]
      localizedAutomorphismFunctorTangent P := by
  letI := naturalLocalizedTangentAddCommGroup P hp.satisfiesRS
  letI := naturalLocalizedTangentModule P hp.satisfiesRS
  let e := (linearLiftEquiv L (FGModuleCat.of k (ULift.{v} k))).trans
    (localizedTangentEquivAut hp.predeformation x₀ P).symm
  have he : ∀ c, localizedTangentEquivAut hp.predeformation x₀ P (e c) =
      linearLiftEquiv L (FGModuleCat.of k (ULift.{v} k)) c :=
    fun c => (localizedTangentEquivAut hp.predeformation x₀ P).apply_symm_apply _
  refine { e with map_add' := ?_, map_smul' := ?_ }
  · intro a b
    apply (localizedTangentEquivAut hp.predeformation x₀ P).injective
    change localizedTangentEquivAut hp.predeformation x₀ P (e (a + b)) =
      localizedTangentEquivAut hp.predeformation x₀ P (e a + e b)
    rw [localizedTangentEquivAut_add hp x₀ P, he, he, he]
    exact linearLiftEquiv_transport_add (squareZeroAlgFunctor (p.obj x₀.val)) P L
      (FGModuleCat.of k (ULift.{v} k)) a b
  · intro r a
    apply (localizedTangentEquivAut hp.predeformation x₀ P).injective
    change localizedTangentEquivAut hp.predeformation x₀ P (e (r • a)) =
      localizedTangentEquivAut hp.predeformation x₀ P ((RingHom.id k) r • e a)
    rw [localizedTangentEquivAut_smul hp x₀ P, he, he]
    exact (linearLiftEquiv_smul L (FGModuleCat.of k (ULift.{v} k)) r a).trans
      (comp_automorphismFunctor_map_smul_id P r _)

private def fieldMultiplication
    {k : Type v} {l : Type w} [Field k] [Field l] [Algebra k l] [Module.Finite k l] (a : l) :
    FGModuleCat.of k (ULift.{v} l) ⟶ FGModuleCat.of k (ULift.{v} l) :=
  FGModuleCat.ofHom
    { toFun := fun x => ⟨a * x.down⟩
      map_add' := fun x y => ULift.ext (mul_add a x.down y.down)
      map_smul' := fun r x => by
        apply ULift.ext
        change a * (r • x.down) = r • (a * x.down)
        simp only [Algebra.smul_def, mul_left_comm] }

private lemma comparisonSquareZero_scaling
    (S : Deformation.ChangeOfFieldsSituation.{u, v, w})
    (A : Deformation.ArtinianLocalAlgCat.{u, max v w, v} S.Λ S.k)
    (B : Deformation.ArtinianLocalAlgCat.{u, max v w, w} S.Λ S.l) (c : S.l) :
    ((squareZeroAlgFunctor A).map (fieldMultiplication (k := S.k) c)).right ≫
        (comparisonSquareZeroIso S A B).hom =
      (comparisonSquareZeroIso S A B).hom ≫ (Deformation.comparisonFunctor S).functor.map
        (((squareZeroAlgFunctor B).map (c • 𝟙 (FGModuleCat.of S.l (ULift.{v} S.l)))).right) := by
  apply Deformation.ArtinianLocalAlgCat.hom_ext
  apply AlgHom.ext
  intro a
  apply ((Deformation.comparisonFunctor S).pullbackEquiv _).injective
  apply Subtype.ext
  change ((Deformation.comparisonFunctor S).pullbackEquiv _
    (comparisonSquareZeroEquiv S A B _)).val = _
  rw [comparisonSquareZeroEquiv_coordinates]
  apply Prod.ext
  · refine Eq.trans ?_ ((Deformation.comparisonFunctor S).map_fst _ _).symm
    apply TrivSqZeroExt.ext
    · refine Eq.trans ?_ (squareZeroAlgFunctor_map_fst B
        (c • 𝟙 (FGModuleCat.of S.l (ULift.{v} S.l))) _).symm
      refine (congrArg (algebraMap S.k S.l)
        (squareZeroAlgFunctor_map_fst A (fieldMultiplication (k := S.k) c) a)).trans ?_
      exact (congrArg (fun x => x.1.fst) (comparisonSquareZeroEquiv_coordinates S A B a)).symm
    · refine Eq.trans ?_ (squareZeroAlgFunctor_map_snd B
        (c • 𝟙 (FGModuleCat.of S.l (ULift.{v} S.l))) _).symm
      refine (squareZeroAlgFunctor_map_snd A (fieldMultiplication (k := S.k) c) a).trans ?_
      refine Eq.trans ?_ (congrArg (fun x : (ULift.{v} S.l) => (c • 𝟙
        (FGModuleCat.of S.l (ULift.{v} S.l))).hom.hom x)
          (congrArg (fun y => TrivSqZeroExt.snd y.1)
            (comparisonSquareZeroEquiv_coordinates S A B a))).symm
      rfl
  · refine Eq.trans ?_ ((Deformation.comparisonFunctor S).map_snd _ _).symm
    exact (squareZeroAlgFunctor_map_fst A (fieldMultiplication (k := S.k) c) a).trans
      (congrArg Prod.snd (comparisonSquareZeroEquiv_coordinates S A B a)).symm

private lemma chosenPushforward_map_base
    {C : Type u} [Category.{v} C] {F : Type y} [Category.{z} F]
    {p : F ⥤ C} {x : F} (P : ChosenPushforwardsAt p x)
    {U V : Under (p.obj x)} (f : U ⟶ V) :
    p.map (P.map f) = eqToHom (P.obj U).property ≫ f.right ≫
      eqToHom (P.obj V).property.symm := by
  let := P.map_isHomLift f
  simpa using IsHomLift.fac' p f.right (P.map f)

private lemma chosenPushforward_hom_ext
    {C : Type u} [Category.{v} C] {F : Type y} [Category.{z} F]
    {p : F ⥤ C} {x : F} (P : ChosenPushforwardsAt p x)
    (U : Under (p.obj x)) {Y : F} (f g : (P.obj U).val ⟶ Y)
    (hb : p.map f = p.map g) (hi : P.inclusion U ≫ f = P.inclusion U ≫ g) : f = g := by
  let b := eqToHom (P.obj U).property.symm ≫ p.map f
  let := P.inclusion_cocartesian U
  let : p.IsHomLift b f := IsHomLift.of_fac' p b f (P.obj U).property rfl (by simp [b])
  let : p.IsHomLift b g := IsHomLift.of_fac' p b g (P.obj U).property rfl (by simp [b, hb])
  exact Functor.IsStronglyCocartesian.ext p U.hom (P.inclusion U) b hi

private lemma pushforwardComparison_natural
    {C : Type u} [Category.{v} C] {F : Type y} [Category.{z} F]
    {D : Type w} [Category.{x} D] (p : F ⥤ C) (G : D ⥤ C)
    {X : F} (P : ChosenPushforwardsAt p X)
    {Y : CategoricalPullback p G}
    (Q : ChosenPushforwardsAt (CategoricalPullback.π₂ p G) Y)
    (U : Under (p.obj X)) (V : Under Y.snd)
    (j : X ⟶ Y.fst) (h : (P.obj U).val ⟶ (Q.obj V).val.fst)
    (hi : P.inclusion U ≫ h = j ≫ (Q.inclusion V).fst)
    (e : U.right ⟶ G.obj V.right)
    (he : eqToHom (P.obj U).property.symm ≫ p.map h ≫
      (Q.obj V).val.iso.hom ≫ G.map (eqToHom (Q.obj V).property) = e)
    (f : U ⟶ U) (g : V ⟶ V)
    (hfg : f.right ≫ e = e ≫ G.map g.right) :
    P.map f ≫ h = h ≫ (Q.map g).fst := by
  apply chosenPushforward_hom_ext P U
  · apply (cancel_epi (eqToHom (P.obj U).property.symm)).mp
    apply (cancel_mono ((Q.obj V).val.iso.hom ≫ G.map (eqToHom (Q.obj V).property))).mp
    have hq : (Q.map g).snd = eqToHom (Q.obj V).property ≫ g.right ≫
        eqToHom (Q.obj V).property.symm := chosenPushforward_map_base Q g
    have hl : eqToHom (P.obj U).property.symm ≫ p.map (P.map f ≫ h) ≫
        (Q.obj V).val.iso.hom ≫ G.map (eqToHom (Q.obj V).property) = f.right ≫ e := by
      rw [p.map_comp, chosenPushforward_map_base]
      simpa only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp] using
        congrArg (fun a => f.right ≫ a) he
    have hr : eqToHom (P.obj U).property.symm ≫ p.map (h ≫ (Q.map g).fst) ≫
        (Q.obj V).val.iso.hom ≫ G.map (eqToHom (Q.obj V).property) = e ≫ G.map g.right := by
      rw [p.map_comp, Category.assoc, ← Category.assoc (p.map (Q.map g).fst), (Q.map g).w]
      rw [hq]
      simpa only [G.map_comp, eqToHom_map, Category.assoc, eqToHom_trans_assoc,
        eqToHom_refl, Category.id_comp, Category.comp_id, eqToHom_trans] using
          congrArg (fun a => a ≫ G.map g.right) he
    simpa only [Category.assoc] using hl.trans (hfg.trans hr.symm)
  · rw [← Category.assoc, P.inclusion_map]
    rw [← Category.assoc, hi, Category.assoc]
    have hq := congrArg CategoricalPullback.Hom.fst (Q.inclusion_map g)
    exact congrArg (fun a => j ≫ a) hq.symm

private lemma pullbackConjugate_transport
    {C : Type u} [Category.{v} C] {F : Type y} [Category.{z} F]
    {D : Type w} [Category.{x} D] (p : F ⥤ C) (G : D ⥤ C)
    {X : F} (P : ChosenPushforwardsAt p X)
    {Y : CategoricalPullback p G}
    (Q : ChosenPushforwardsAt (CategoricalPullback.π₂ p G) Y)
    (U : Under (p.obj X)) (V : Under Y.snd)
    (H : (P.obj U).val ≅ (Q.obj V).val.fst)
    (f : U ⟶ U) (g : V ⟶ V)
    (hfg : P.map f ≫ H.hom = H.hom ≫ (Q.map g).fst) (a : Aut (P.obj U)) :
    let E := (fiberAutConjugateEquiv p (P.obj U)
      (Functor.Fiber.mk (p := p) (a := (Q.obj V).val.fst) rfl) H).trans
      (pullbackFiberAutEquiv p G (Q.obj V))
    E (P.transportAutHom f a) = Q.transportAutHom g (E a) := by
  let E := (fiberAutConjugateEquiv p (P.obj U)
    (Functor.Fiber.mk (p := p) (a := (Q.obj V).val.fst) rfl) H).trans
    (pullbackFiberAutEquiv p G (Q.obj V))
  apply pullbackAut_fst_injective p G (Q.obj V)
  apply (cancel_epi H.hom).mp
  have hE (a : Aut (P.obj U)) : a.asIso.hom.val ≫ H.hom = H.hom ≫ (E a).asIso.hom.val.fst :=
    fiberAutConjugateEquiv_comm p (P.obj U)
      (Functor.Fiber.mk (p := p) (a := (Q.obj V).val.fst) rfl) H a
  rw [← hE]
  let := P.map_cocartesian f
  let lhs := (P.transportAutHom f a).asIso.hom.val
  let rhs := H.hom ≫ (Q.transportAutHom g (E a)).asIso.hom.val.fst ≫ H.inv
  have hmap : p.map rhs = 𝟙 (p.obj (P.obj U).val) := by
    simp only [rhs, p.map_comp, pullbackAut_fst_map_eq_id, Category.id_comp,
      ← p.map_comp, H.hom_inv_id, p.map_id]
  have heq : lhs = rhs := by
    let : p.IsHomLift (𝟙 U.right) lhs := (P.transportAutHom f a).asIso.hom.property
    let : p.IsHomLift (𝟙 U.right) rhs := by
      apply IsHomLift.of_fac' p _ _ (P.obj U).property (P.obj U).property
      simp [hmap]
    apply Functor.IsStronglyCocartesian.ext p f.right (P.map f) (𝟙 U.right)
    change P.map f ≫ (P.transportAutHom f a).asIso.hom.val = P.map f ≫ rhs
    have hmt : P.map f ≫ (P.transportAutHom f a).asIso.hom.val = a.asIso.hom.val ≫ P.map f :=
      P.map_transportHom f a
    rw [hmt]
    dsimp [rhs]
    have hq := congrArg CategoricalPullback.Hom.fst (Q.map_transportHom g (E a))
    change (Q.map g).fst ≫ (Q.transportAutHom g (E a)).asIso.hom.val.fst =
      (E a).asIso.hom.val.fst ≫ (Q.map g).fst at hq
    calc
      a.asIso.hom.val ≫ P.map f = (a.asIso.hom.val ≫ H.hom) ≫ (Q.map g).fst ≫ H.inv := by
        rw [Category.assoc, ← Category.assoc H.hom, ← hfg, Category.assoc,
          Iso.hom_inv_id, Category.comp_id]
      _ = (H.hom ≫ (E a).asIso.hom.val.fst) ≫ (Q.map g).fst ≫ H.inv := by rw [hE]
      _ = H.hom ≫ ((Q.map g).fst ≫ (Q.transportAutHom g (E a)).asIso.hom.val.fst) ≫ H.inv := by
        rw [hq]
        simp only [Category.assoc]
      _ = P.map f ≫ (H.hom ≫ (Q.transportAutHom g (E a)).asIso.hom.val.fst ≫ H.inv) := by
        rw [← Category.assoc (P.map f), hfg]
        simp only [Category.assoc]
  change lhs ≫ H.hom = _
  rw [heq]
  simp only [rhs, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rfl

private noncomputable def scalarExtensionEquiv
    (k : Type v) (l : Type w) [Field k] [Field l] [Algebra k l] [Module.Finite k l]
    (L : FGModuleCat.{max v w} k ⥤ ModuleCat.{z} k) [L.Additive] [L.Linear k]
    (T : Type a) [AddCommGroup T] [Module k T]
    (U : Type u₁) [AddCommGroup U] [Module l U]
    (eK : (L.obj (FGModuleCat.of k (ULift.{w} k)) : Type z) ≃ₗ[k] T)
    (eV : (L.obj (FGModuleCat.of k (ULift.{v} l)) : Type z) ≃+ U)
    (hscale : ∀ (c : l) x, eV (L.map (fieldMultiplication (k := k) c) x) = c • eV x) :
    { E : TensorProduct k l T ≃ₗ[l] U // ∀ (c : l) (t : T),
      E (c ⊗ₜ[k] t) = eV (L.map
        (tensorFromUnitLifted k (FGModuleCat.of k (ULift.{v} l)) (ULift.up c)) (eK.symm t)) } := by
  let K := L.obj (FGModuleCat.of k (ULift.{w} k))
  let V := FGModuleCat.of k (ULift.{v} l)
  let e : TensorProduct k l T ≃ₗ[k] L.obj V :=
    (TensorProduct.congr (ULift.moduleEquiv.symm : l ≃ₗ[k] ULift.{v} l) eK.symm).trans
      ((TensorProduct.comm k (ULift.{v} l) K).trans
        (tensorComparisonLinearEquivLifted k L K (LinearEquiv.refl k K) V))
  let f := e.toAddEquiv.trans eV
  have ht (c : l) (t : T) : f (c ⊗ₜ[k] t) =
      eV (L.map (tensorFromUnitLifted k V (ULift.up c)) (eK.symm t)) := rfl
  have hs (c : l) (t : TensorProduct k l T) : f (c • t) = c • f t := by
    induction t using TensorProduct.inductionOn with
    | add x y hx hy => simp only [smul_add, map_add, hx, hy]
    | tmul r t =>
      rw [TensorProduct.smul_tmul', smul_eq_mul, ht, ht]
      have h : tensorFromUnitLifted k V (ULift.up (c * r)) =
          tensorFromUnitLifted k V (ULift.up r) ≫ fieldMultiplication (k := k) c := by
        apply FGModuleCat.hom_ext
        apply LinearMap.ext
        intro a
        apply ULift.ext
        change a.down • (c * r) = c * (a.down • r)
        simp only [Algebra.smul_def, mul_left_comm]
      rw [h, L.map_comp, ModuleCat.comp_apply, hscale]
  exact ⟨{ f.toEquiv with map_add' := f.map_add, map_smul' := hs }, ht⟩

/-- Two scalar-extension equivalences pinned as in Tag 07WC agree: the morphism of chosen
points and the comparison of their dual-number pushforwards are each unique, and pure tensors
generate the scalar extension. -/
private theorem unique_infinitesimalAutomorphismsChangeOfFields
    (S : Deformation.ChangeOfFieldsSituation.{u, v, w})
    {F : Type y} [Category.{z} F]
    (p : F ⥤ Deformation.ArtinianLocalAlgCat.{u, max v w, v} S.Λ S.k)
    (hp : Deformation.IsDeformationCategory p)
    (x₀ : p.Fiber (residueFieldObject.{u, w, v} S.Λ S.k))
    (P : ChosenPushforwardsAt p x₀.1)
    (xₗ : (Deformation.changeOfFieldsProjection S p).Fiber
      (residueFieldObject.{u, v, w} S.Λ S.l))
    (Q : ChosenPushforwardsAt
      (Deformation.changeOfFieldsProjection S p) xₗ.1) :
    let hq := changeOfFieldsProjection_satisfiesRS
      S p hp.satisfiesRS
    letI : AddCommGroup (localizedAutomorphismFunctorTangent P) :=
      naturalLocalizedTangentAddCommGroup P hp.satisfiesRS
    letI : Module S.k (localizedAutomorphismFunctorTangent P) :=
      naturalLocalizedTangentModule P hp.satisfiesRS
    letI : AddCommGroup (localizedAutomorphismFunctorTangent Q) :=
      naturalLocalizedTangentAddCommGroup Q hq
    letI : Module S.l (localizedAutomorphismFunctorTangent Q) :=
      naturalLocalizedTangentModule Q hq
    let Uε := dualNumbersUnder (p := p) (x := x₀.1)
    let Vε := dualNumbersUnder
      (p := Deformation.changeOfFieldsProjection S p) (x := xₗ.1)
    ∀ E₁ E₂ : TensorProduct S.k S.l
        (localizedAutomorphismFunctorTangent P) ≃ₗ[S.l]
        localizedAutomorphismFunctorTangent Q,
      (∃ (j : x₀.1 ⟶ xₗ.1.fst) (h : (P.obj Uε).1 ⟶ (Q.obj Vε).1.fst),
        let b : Uε.right ⟶
            (Deformation.comparisonFunctor.{u, v, w, max v w} S).functor.obj Vε.right :=
          eqToHom (P.obj Uε).2.symm ≫ p.map h ≫ (Q.obj Vε).1.iso.hom ≫
            (Deformation.comparisonFunctor.{u, v, w, max v w} S).functor.map (eqToHom (Q.obj Vε).2)
        (P.inclusion Uε ≫ h = j ≫ (Q.inclusion Vε).fst) ∧
        (∀ a : Uε.right,
          ((((Deformation.comparisonFunctor.{u, v, w, max v w} S).pullbackEquiv
              Vε.right) (b.hom a)).val.1).fst = algebraMap S.k S.l a.fst ∧
          ((((Deformation.comparisonFunctor.{u, v, w, max v w} S).pullbackEquiv
              Vε.right) (b.hom a)).val.1).snd =
            ULift.up (algebraMap S.k S.l a.snd.down) ∧
          (((Deformation.comparisonFunctor.{u, v, w, max v w} S).pullbackEquiv
              Vε.right) (b.hom a)).val.2 = a.fst) ∧
        (∀ t : localizedAutomorphismFunctorTangent P,
          (localizedTangentEquivKernel P t).1.asIso.hom.val ≫ h =
            h ≫ (localizedTangentEquivKernel Q
              (E₁ (1 ⊗ₜ[S.k] t))).1.asIso.hom.val.fst)) →
      (∃ (j : x₀.1 ⟶ xₗ.1.fst) (h : (P.obj Uε).1 ⟶ (Q.obj Vε).1.fst),
        let b : Uε.right ⟶
            (Deformation.comparisonFunctor.{u, v, w, max v w} S).functor.obj Vε.right :=
          eqToHom (P.obj Uε).2.symm ≫ p.map h ≫ (Q.obj Vε).1.iso.hom ≫
            (Deformation.comparisonFunctor.{u, v, w, max v w} S).functor.map (eqToHom (Q.obj Vε).2)
        (P.inclusion Uε ≫ h = j ≫ (Q.inclusion Vε).fst) ∧
        (∀ a : Uε.right,
          ((((Deformation.comparisonFunctor.{u, v, w, max v w} S).pullbackEquiv
              Vε.right) (b.hom a)).val.1).fst = algebraMap S.k S.l a.fst ∧
          ((((Deformation.comparisonFunctor.{u, v, w, max v w} S).pullbackEquiv
              Vε.right) (b.hom a)).val.1).snd =
            ULift.up (algebraMap S.k S.l a.snd.down) ∧
          (((Deformation.comparisonFunctor.{u, v, w, max v w} S).pullbackEquiv
              Vε.right) (b.hom a)).val.2 = a.fst) ∧
        (∀ t : localizedAutomorphismFunctorTangent P,
          (localizedTangentEquivKernel P t).1.asIso.hom.val ≫ h =
            h ≫ (localizedTangentEquivKernel Q
              (E₂ (1 ⊗ₜ[S.k] t))).1.asIso.hom.val.fst)) →
      E₁ = E₂ := by
  classical
  extract_lets hq Uε Vε
  let := naturalLocalizedTangentAddCommGroup P hp.satisfiesRS
  let := naturalLocalizedTangentModule P hp.satisfiesRS
  let := naturalLocalizedTangentAddCommGroup Q hq
  let := naturalLocalizedTangentModule Q hq
  intro E₁ E₂ hE₁ hE₂
  rcases hE₁ with ⟨j₁, h₁, hc₁, hb₁, ha₁⟩
  rcases hE₂ with ⟨j₂, h₂, hc₂, hb₂, ha₂⟩
  let : Unique (x₀.val ⟶ xₗ.val.fst) :=
    (unique_hom_changeOfFields_point S p hp.predeformation x₀ xₗ).some
  have hj : j₁ = j₂ := Subsingleton.elim _ _
  have hb : eqToHom (P.obj Uε).2.symm ≫ p.map h₁ ≫ (Q.obj Vε).1.iso.hom ≫
      (Deformation.comparisonFunctor.{u, v, w, max v w} S).functor.map
        (eqToHom (Q.obj Vε).2) =
      eqToHom (P.obj Uε).2.symm ≫ p.map h₂ ≫ (Q.obj Vε).1.iso.hom ≫
      (Deformation.comparisonFunctor.{u, v, w, max v w} S).functor.map
        (eqToHom (Q.obj Vε).2) := by
    apply Deformation.ArtinianLocalAlgCat.hom_ext
    apply AlgHom.ext
    intro a
    apply ((Deformation.comparisonFunctor.{u, v, w, max v w} S).pullbackEquiv
      Vε.right).injective
    apply Subtype.ext
    apply Prod.ext
    · apply TrivSqZeroExt.ext
      · exact (hb₁ a).1.trans (hb₂ a).1.symm
      · exact (hb₁ a).2.1.trans (hb₂ a).2.1.symm
    · exact (hb₁ a).2.2.trans (hb₂ a).2.2.symm
  have hmap : p.map h₁ = p.map h₂ := by
    apply (cancel_epi (eqToHom (P.obj Uε).2.symm)).mp
    apply (cancel_mono ((Q.obj Vε).1.iso.hom ≫
      (Deformation.comparisonFunctor.{u, v, w, max v w} S).functor.map (eqToHom (Q.obj Vε).2))).mp
    rw [Category.assoc, Category.assoc]
    exact hb
  have hh : h₁ = h₂ :=
    chosenPushforward_hom_ext P Uε h₁ h₂ hmap (hc₁.trans (by rw [hj]; exact hc₂.symm))
  have ht (t : localizedAutomorphismFunctorTangent P) :
      E₁ (1 ⊗ₜ[S.k] t) = E₂ (1 ⊗ₜ[S.k] t) := by
    apply (localizedTangentEquivKernel Q).injective
    apply Subtype.ext
    apply pullbackAut_fst_injective p
      (Deformation.comparisonFunctor.{u, v, w, max v w} S).functor (Q.obj Vε)
    let a₁ := (localizedTangentEquivKernel Q (E₁ (1 ⊗ₜ[S.k] t))).1
    let a₂ := (localizedTangentEquivKernel Q (E₂ (1 ⊗ₜ[S.k] t))).1
    have hfst : a₁.asIso.hom.val.fst = a₂.asIso.hom.val.fst := by
      let : p.IsStronglyCocartesian (p.map h₁) h₁ :=
        isStronglyCocartesian_of_isCofiberedInGroupoids hp.predeformation.cofibered _ _
          (IsHomLift.map p h₁)
      let := pullbackAut_fst_isHomLift p
        (Deformation.comparisonFunctor.{u, v, w, max v w} S).functor (Q.obj Vε) a₁
      let := pullbackAut_fst_isHomLift p
        (Deformation.comparisonFunctor.{u, v, w, max v w} S).functor (Q.obj Vε) a₂
      apply Functor.IsStronglyCocartesian.ext p (p.map h₁) h₁
        (𝟙 (p.obj (Q.obj Vε).1.fst))
      exact (ha₁ t).symm.trans (by rw [hh]; exact ha₂ t)
    exact hfst
  apply LinearEquiv.toLinearMap_injective
  apply LinearMap.ext
  intro t
  change E₁ t = E₂ t
  induction t using TensorProduct.inductionOn with
  | tmul a t =>
    have h := congrArg (fun x => a • x) (ht t)
    simpa only [← map_smul, TensorProduct.smul_tmul', smul_eq_mul, mul_one] using h
  | add a b ha hb => simpa only [map_add] using congrArg₂ (· + ·) ha hb

/-- A scalar-extension equivalence pinned as in Tag 07WC exists: the automorphism functor on
square-zero extensions of the residue field has a linear lift, and a linear functor on
finite-dimensional vector spaces is tensoring with its value on the ground field. -/
private theorem exists_infinitesimalAutomorphismsChangeOfFields
    (S : Deformation.ChangeOfFieldsSituation.{u, v, w})
    {F : Type y} [Category.{z} F]
    (p : F ⥤ Deformation.ArtinianLocalAlgCat.{u, max v w, v} S.Λ S.k)
    (hp : Deformation.IsDeformationCategory p)
    (x₀ : p.Fiber (residueFieldObject.{u, w, v} S.Λ S.k))
    (P : ChosenPushforwardsAt p x₀.1)
    (xₗ : (Deformation.changeOfFieldsProjection S p).Fiber
      (residueFieldObject.{u, v, w} S.Λ S.l))
    (Q : ChosenPushforwardsAt
      (Deformation.changeOfFieldsProjection S p) xₗ.1) :
    let hq := changeOfFieldsProjection_satisfiesRS
      S p hp.satisfiesRS
    letI : AddCommGroup (localizedAutomorphismFunctorTangent P) :=
      naturalLocalizedTangentAddCommGroup P hp.satisfiesRS
    letI : Module S.k (localizedAutomorphismFunctorTangent P) :=
      naturalLocalizedTangentModule P hp.satisfiesRS
    letI : AddCommGroup (localizedAutomorphismFunctorTangent Q) :=
      naturalLocalizedTangentAddCommGroup Q hq
    letI : Module S.l (localizedAutomorphismFunctorTangent Q) :=
      naturalLocalizedTangentModule Q hq
    let Uε := dualNumbersUnder (p := p) (x := x₀.1)
    let Vε := dualNumbersUnder
      (p := Deformation.changeOfFieldsProjection S p) (x := xₗ.1)
    ∃ E : TensorProduct S.k S.l
        (localizedAutomorphismFunctorTangent P) ≃ₗ[S.l]
        localizedAutomorphismFunctorTangent Q,
      ∃ (j : x₀.1 ⟶ xₗ.1.fst) (h : (P.obj Uε).1 ⟶ (Q.obj Vε).1.fst),
        let b : Uε.right ⟶
            (Deformation.comparisonFunctor.{u, v, w, max v w} S).functor.obj Vε.right :=
          eqToHom (P.obj Uε).2.symm ≫ p.map h ≫ (Q.obj Vε).1.iso.hom ≫
            (Deformation.comparisonFunctor.{u, v, w, max v w} S).functor.map (eqToHom (Q.obj Vε).2)
        (P.inclusion Uε ≫ h = j ≫ (Q.inclusion Vε).fst) ∧
        (∀ a : Uε.right,
          ((((Deformation.comparisonFunctor.{u, v, w, max v w} S).pullbackEquiv
              Vε.right) (b.hom a)).val.1).fst = algebraMap S.k S.l a.fst ∧
          ((((Deformation.comparisonFunctor.{u, v, w, max v w} S).pullbackEquiv
              Vε.right) (b.hom a)).val.1).snd =
            ULift.up (algebraMap S.k S.l a.snd.down) ∧
          (((Deformation.comparisonFunctor.{u, v, w, max v w} S).pullbackEquiv
              Vε.right) (b.hom a)).val.2 = a.fst) ∧
        (∀ t : localizedAutomorphismFunctorTangent P,
          (localizedTangentEquivKernel P t).1.asIso.hom.val ≫ h =
            h ≫ (localizedTangentEquivKernel Q
              (E (1 ⊗ₜ[S.k] t))).1.asIso.hom.val.fst) := by
  classical
  extract_lets hq Uε Vε
  let := naturalLocalizedTangentAddCommGroup P hp.satisfiesRS
  let := naturalLocalizedTangentModule P hp.satisfiesRS
  let := naturalLocalizedTangentAddCommGroup Q hq
  let := naturalLocalizedTangentModule Q hq
  let q := Deformation.changeOfFieldsProjection.{u, v, w, max v w, y, z} S p
  let G := (Deformation.comparisonFunctor S).functor
  have hp' : IsPredeformationCategory.{u, max v w, v} p := by
    refine ⟨hp.predeformation.cofibered, ?_⟩
    apply (CategoryTheory.equiv_punit_iff_unique (C := _)).mpr
    exact cofibered_fiber_unique_of_iso p hp.predeformation.cofibered
      (residueFieldObjectULiftIso.{u, w, v} S.Λ S.k).symm
      ((CategoryTheory.equiv_punit_iff_unique (C := _)).mp hp.predeformation.specialFiber)
  let hqpre :=
    changeOfFieldsProjection_isPredeformationCategory.{u, v, w, v}
      S p hp'
  let hqdef : Deformation.IsDeformationCategory q := ⟨hqpre, hq⟩
  let L := automorphismFunctor_squareZero_linearLift hp x₀ P
  let K := FGModuleCat.of S.k (ULift.{w} S.k)
  let V := FGModuleCat.of S.k (ULift.{v} S.l)
  let W := (squareZeroAlgFunctor (p.obj x₀.val)).obj V
  let j := (unique_hom_changeOfFields_point S p hp.predeformation x₀ xₗ).some.default
  let Hdata := comparisonPushforward S p hp.predeformation.cofibered P Q j
  let H := Hdata.val
  let eAut := (fiberAutConjugateEquiv p (P.obj W)
    (Functor.Fiber.mk (p := p) (a := (Q.obj Vε).val.fst) rfl) H).trans
    (pullbackFiberAutEquiv p G (Q.obj Vε))
  let eQ := localizedTangentEquivAut hqpre xₗ Q
  let ev := (linearLiftEquiv L V).trans (eAut.toEquiv.trans eQ.symm)
  have hev (a : L.functor.obj V) : eQ (ev a) = eAut (linearLiftEquiv L V a) :=
    eQ.apply_symm_apply _
  let eV : (L.functor.obj V : Type z) ≃+ localizedAutomorphismFunctorTangent Q :=
    { toEquiv := ev
      map_add' := by
        intro a b
        apply eQ.injective
        change eQ (ev (a + b)) = eQ (ev a + ev b)
        rw [hev, localizedTangentEquivAut_add hqdef, hev, hev]
        rw [linearLiftEquiv_transport_add (squareZeroAlgFunctor (p.obj x₀.val)) P L]
        exact eAut.map_mul _ _ }
  have hscale (c : S.l) (a : L.functor.obj V) :
      eV (L.functor.map (fieldMultiplication (k := S.k) c) a) = c • eV a := by
    let f := (squareZeroAlgFunctor (p.obj x₀.val)).map (fieldMultiplication (k := S.k) c)
    let g := tangentScaling (p := q) (x := xₗ.val) c
    have hn : P.map f ≫ H.hom = H.hom ≫ (Q.map g).fst :=
      pushforwardComparison_natural p G P Q W Vε j H.hom Hdata.property.1
        (comparisonSquareZeroIso S (p.obj x₀.val) xₗ.val.snd).hom Hdata.property.2 f g
        (comparisonSquareZero_scaling S (p.obj x₀.val) xₗ.val.snd c)
    apply eQ.injective
    change eQ (ev (L.functor.map (fieldMultiplication (k := S.k) c) a)) = eQ (c • ev a)
    rw [localizedTangentEquivAut_smul hqdef, hev, hev]
    change eAut (linearLiftEquiv L V (L.functor.map (fieldMultiplication (k := S.k) c) a)) =
      Q.transportAutHom g (eAut (linearLiftEquiv L V a))
    rw [linearLiftEquiv_map]
    exact pullbackConjugate_transport p G P Q W Vε H f g hn _
  let eK := linearLiftTangentEquiv hp x₀ P L
  let Edata := scalarExtensionEquiv S.k S.l L.functor
    (localizedAutomorphismFunctorTangent P)
    (localizedAutomorphismFunctorTangent Q) eK eV hscale
  let E := Edata.val
  let f : Uε ⟶ W := (squareZeroAlgFunctor (p.obj x₀.val)).map
    (tensorFromUnitLifted S.k V (ULift.up (1 : S.l)))
  let h := P.map f ≫ H.hom
  refine ⟨E, j, h, ?_, ?_, ?_⟩
  · have hinc : P.inclusion Uε ≫ P.map f ≫ H.hom = j ≫ (Q.inclusion Vε).fst :=
      ((Category.assoc (P.inclusion Uε) (P.map f) H.hom).symm.trans
        (congrArg (fun m => m ≫ H.hom) (P.inclusion_map f))).trans Hdata.property.1
    exact hinc
  · have hbG : eqToHom (P.obj Uε).property.symm ≫ p.map h ≫
        (Q.obj Vε).val.iso.hom ≫ G.map (eqToHom (Q.obj Vε).property) =
        f.right ≫ (comparisonSquareZeroIso S (p.obj x₀.val) xₗ.val.snd).hom := by
      have hsplit : p.map (P.map f ≫ H.hom) = p.map (P.map f) ≫ p.map H.hom :=
        p.map_comp _ _
      have hbase : p.map (P.map f) = eqToHom (P.obj Uε).property ≫ f.right ≫
          eqToHom (P.obj W).property.symm := chosenPushforward_map_base P f
      have hH : eqToHom (P.obj W).property.symm ≫ p.map H.hom ≫
          (Q.obj Vε).val.iso.hom ≫ G.map (eqToHom (Q.obj Vε).property) =
          (comparisonSquareZeroIso S (p.obj x₀.val) xₗ.val.snd).hom := Hdata.property.2
      have step1 : eqToHom (P.obj Uε).property.symm ≫ p.map h ≫
          (Q.obj Vε).val.iso.hom ≫ G.map (eqToHom (Q.obj Vε).property) =
          eqToHom (P.obj Uε).property.symm ≫ (p.map (P.map f) ≫ p.map H.hom) ≫
            (Q.obj Vε).val.iso.hom ≫ G.map (eqToHom (Q.obj Vε).property) := by
        rw [hsplit]
      have step2 : eqToHom (P.obj Uε).property.symm ≫
          (p.map (P.map f) ≫ p.map H.hom) ≫
            (Q.obj Vε).val.iso.hom ≫ G.map (eqToHom (Q.obj Vε).property) =
          f.right ≫ eqToHom (P.obj W).property.symm ≫ p.map H.hom ≫
            (Q.obj Vε).val.iso.hom ≫ G.map (eqToHom (Q.obj Vε).property) := by
        rw [hbase]
        simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
      exact step1.trans (step2.trans (congrArg (fun m => f.right ≫ m) hH))
    have hb : eqToHom (P.obj Uε).property.symm ≫ p.map h ≫
        (Q.obj Vε).val.iso.hom ≫
          (Deformation.comparisonFunctor.{u, v, w, max v w} S).functor.map
            (eqToHom (Q.obj Vε).property) =
        f.right ≫ (comparisonSquareZeroIso S (p.obj x₀.val) xₗ.val.snd).hom := hbG
    intro a
    have hBa : (eqToHom (P.obj Uε).property.symm ≫ p.map h ≫
        (Q.obj Vε).val.iso.hom ≫
          (Deformation.comparisonFunctor.{u, v, w, max v w} S).functor.map
            (eqToHom (Q.obj Vε).property)).hom a =
        (comparisonSquareZeroIso S (p.obj x₀.val) xₗ.val.snd).hom.hom (f.right.hom a) :=
      congrArg (fun m : Uε.right ⟶
        (Deformation.comparisonFunctor.{u, v, w, max v w} S).functor.obj Vε.right =>
          m.hom a) hb
    have hc := comparisonSquareZeroEquiv_coordinates S (p.obj x₀.val) xₗ.val.snd (f.right.hom a)
    have hfst : (f.right.hom a).fst = a.fst :=
      squareZeroAlgFunctor_map_fst (p.obj x₀.val) _ a
    have hsnd : (f.right.hom a).snd = ULift.up (algebraMap S.k S.l a.snd.down) :=
      (squareZeroAlgFunctor_map_snd (p.obj x₀.val) _ a).trans (by
        apply ULift.ext
        change a.snd.down • (1 : S.l) = algebraMap S.k S.l a.snd.down
        rw [Algebra.smul_def, mul_one])
    refine ⟨?_, ?_, ?_⟩
    · exact (congrArg (fun z =>
        ((((Deformation.comparisonFunctor.{u, v, w, max v w} S).pullbackEquiv
          Vε.right) z).val.1).fst) hBa).trans
          ((congrArg (fun x => x.1.fst) hc).trans (congrArg (algebraMap S.k S.l) hfst))
    · exact (congrArg (fun z =>
        ((((Deformation.comparisonFunctor.{u, v, w, max v w} S).pullbackEquiv
          Vε.right) z).val.1).snd) hBa).trans
          ((congrArg (fun x => x.1.snd) hc).trans hsnd)
    · exact (congrArg (fun z =>
        (((Deformation.comparisonFunctor.{u, v, w, max v w} S).pullbackEquiv
          Vε.right) z).val.2) hBa).trans ((congrArg Prod.snd hc).trans hfst)
  · intro t
    have hK : linearLiftEquiv L K (eK.symm t) =
        localizedTangentEquivAut hp.predeformation x₀ P t := by
      have hh (a : L.functor.obj K) :
          localizedTangentEquivAut hp.predeformation x₀ P (eK a) =
            linearLiftEquiv L K a :=
        (localizedTangentEquivAut hp.predeformation x₀ P).apply_symm_apply _
      exact (hh (eK.symm t)).symm.trans
        (congrArg (localizedTangentEquivAut hp.predeformation x₀ P) (eK.apply_symm_apply t))
    have he : eQ (E (1 ⊗ₜ[S.k] t)) = eAut (P.transportAutHom f
        (localizedTangentEquivAut hp.predeformation x₀ P t)) := by
      rw [Edata.property]
      change eQ (ev (L.functor.map _ (eK.symm t))) = _
      rw [hev, linearLiftEquiv_map, hK]
      rfl
    have hc := fiberAutConjugateEquiv_comm p (P.obj W)
      (Functor.Fiber.mk (p := p) (a := (Q.obj Vε).val.fst) rfl) H
      (P.transportAutHom f (localizedTangentEquivAut hp.predeformation x₀ P t))
    have hmt : P.map f ≫ (P.transportAutHom f
        (localizedTangentEquivAut hp.predeformation x₀ P t)).asIso.hom.val =
        (localizedTangentEquivAut hp.predeformation x₀ P t).asIso.hom.val ≫ P.map f :=
      P.map_transportHom f _
    have hgoal : (localizedTangentEquivAut hp.predeformation x₀ P t).asIso.hom.val ≫
        (P.map f ≫ H.hom) = (P.map f ≫ H.hom) ≫
          (fiberAutConjugateEquiv p (P.obj W)
            (Functor.Fiber.mk (p := p) (a := (Q.obj Vε).val.fst) rfl) H
            (P.transportAutHom f
              (localizedTangentEquivAut hp.predeformation x₀ P t))).asIso.hom.val :=
      ((Category.assoc (localizedTangentEquivAut hp.predeformation x₀ P t).asIso.hom.val
          (P.map f) H.hom).symm.trans
        ((congrArg (fun m => m ≫ H.hom) hmt.symm).trans
          ((Category.assoc (P.map f) (P.transportAutHom f
              (localizedTangentEquivAut hp.predeformation x₀ P t)).asIso.hom.val H.hom).trans
            ((congrArg (fun m => P.map f ≫ m) hc).trans
              (Category.assoc (P.map f) H.hom _).symm))))
    change (localizedTangentEquivAut hp.predeformation x₀ P t).asIso.hom.val ≫ h =
      h ≫ (eQ (E (1 ⊗ₜ[S.k] t))).asIso.hom.val.fst
    rw [he]
    exact hgoal

/-- **Stacks Project, Tag 07WC.** For a deformation category over the residue field `k`, the
space of infinitesimal automorphisms extends by scalars along `k → l` to the space of
infinitesimal automorphisms of the change of residue field. The equivalence is pinned by its
action on dual-number automorphisms, read through a comparison of pushforwards whose base
morphism has the prescribed pullback coordinates. -/
@[stacks 07WC]
public theorem existsUnique_infinitesimalAutomorphismsChangeOfFields
    (S : Deformation.ChangeOfFieldsSituation.{u, v, w})
    {F : Type y} [Category.{z} F]
    (p : F ⥤ Deformation.ArtinianLocalAlgCat.{u, max v w, v} S.Λ S.k)
    (hp : Deformation.IsDeformationCategory p)
    (x₀ : p.Fiber (residueFieldObject.{u, w, v} S.Λ S.k))
    (P : ChosenPushforwardsAt p x₀.1)
    (xₗ : (Deformation.changeOfFieldsProjection S p).Fiber
      (residueFieldObject.{u, v, w} S.Λ S.l))
    (Q : ChosenPushforwardsAt
      (Deformation.changeOfFieldsProjection S p) xₗ.1) :
    let hq := changeOfFieldsProjection_satisfiesRS
      S p hp.satisfiesRS
    letI : AddCommGroup (localizedAutomorphismFunctorTangent P) :=
      naturalLocalizedTangentAddCommGroup P hp.satisfiesRS
    letI : Module S.k (localizedAutomorphismFunctorTangent P) :=
      naturalLocalizedTangentModule P hp.satisfiesRS
    letI : AddCommGroup (localizedAutomorphismFunctorTangent Q) :=
      naturalLocalizedTangentAddCommGroup Q hq
    letI : Module S.l (localizedAutomorphismFunctorTangent Q) :=
      naturalLocalizedTangentModule Q hq
    let Uε := dualNumbersUnder (p := p) (x := x₀.1)
    let Vε := dualNumbersUnder
      (p := Deformation.changeOfFieldsProjection S p) (x := xₗ.1)
    ∃! E : TensorProduct S.k S.l
        (localizedAutomorphismFunctorTangent P) ≃ₗ[S.l]
        localizedAutomorphismFunctorTangent Q,
      ∃ (j : x₀.1 ⟶ xₗ.1.fst) (h : (P.obj Uε).1 ⟶ (Q.obj Vε).1.fst),
        let b : Uε.right ⟶
            (Deformation.comparisonFunctor.{u, v, w, max v w} S).functor.obj Vε.right :=
          eqToHom (P.obj Uε).2.symm ≫ p.map h ≫ (Q.obj Vε).1.iso.hom ≫
            (Deformation.comparisonFunctor.{u, v, w, max v w} S).functor.map (eqToHom (Q.obj Vε).2)
        (P.inclusion Uε ≫ h = j ≫ (Q.inclusion Vε).fst) ∧
        (∀ a : Uε.right,
          ((((Deformation.comparisonFunctor.{u, v, w, max v w} S).pullbackEquiv
              Vε.right) (b.hom a)).val.1).fst = algebraMap S.k S.l a.fst ∧
          ((((Deformation.comparisonFunctor.{u, v, w, max v w} S).pullbackEquiv
              Vε.right) (b.hom a)).val.1).snd =
            ULift.up (algebraMap S.k S.l a.snd.down) ∧
          (((Deformation.comparisonFunctor.{u, v, w, max v w} S).pullbackEquiv
              Vε.right) (b.hom a)).val.2 = a.fst) ∧
        (∀ t : localizedAutomorphismFunctorTangent P,
          (localizedTangentEquivKernel P t).1.asIso.hom.val ≫ h =
            h ≫ (localizedTangentEquivKernel Q
              (E (1 ⊗ₜ[S.k] t))).1.asIso.hom.val.fst) :=
  existsUnique_of_exists_of_unique
    (exists_infinitesimalAutomorphismsChangeOfFields S p hp x₀ P xₗ Q)
    (unique_infinitesimalAutomorphismsChangeOfFields S p hp x₀ P xₗ Q)

end

end Deformation

end
