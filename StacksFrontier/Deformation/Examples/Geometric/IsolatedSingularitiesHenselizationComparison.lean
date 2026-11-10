module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Deformation.Examples.Geometric.IsolatedSingularities
public import StacksFrontier.Deformation.Examples.Geometric.RingDeformationFiberIso
public import StacksFrontier.Deformation.Examples.Geometric.RingDeformationPi

/-!
# Henselizing along `𝔪₁ ∩ … ∩ 𝔪ₙ` is henselizing each local ring

The proof of **Stacks 0DZF** never applies **Stacks 0DZD** to a local ring `P_{𝔪 i}`: that ring
is not of finite type over `k`, so the tag would not apply. It applies 0DZD to `P` *itself*, with
the ideal `J = 𝔪 1 ∩ … ∩ 𝔪 n`, where the finite type hypothesis genuinely holds, obtaining the
henselization functor `𝓓_P → 𝓓_{P^h_J}`; and it then says "`P^h = ∏ P^h_{𝔪 i}`" and reads the
conclusion at the product. Making that last step precise is exactly the content of this file: the
henselization functor at `J` followed by the transport along the ring isomorphism
`P^h_J ≅ ∏ P^h_{𝔪 i}` *is*, up to a natural isomorphism over `𝒞_Λ`, the composite that localizes a
deformation at each `𝔪 i`, henselizes each of the resulting local rings, and reads the family of
deformations so obtained as a deformation of the product ring.

The ring-theoretic heart of the comparison is that henselization commutes with the two operations
being performed on a deformation: for a deformation `X` of `P` with fibre `Q` and `n = 𝔪 Q` the
inverse image of `𝔪`, the henselization of the pair `(Q, n)` is the henselization of the local
ring `Q_n`, and the henselization of `(Q, n₁ ∩ … ∩ nₙ)` is the product of the henselizations of
the `Q_{n i}`. Both statements are applications of the results of
`StacksFrontier.RingTheory.Henselian.Pair.HenselizationAtMaximalIdeals` to the fibre, transported
along the identification of the fibre of a henselized deformation with the henselization of the
fibre.

The comparisons are stated as `Nonempty (F ≅ G)` for based functors `F` and `G`, which is the
form `Deformation.isSmooth_of_iso` and `Deformation.mapIsomorphismClasses_eq_of_iso` consume. The
ring isomorphism the transport is taken along is a *hypothesis*, not an existential, so that a
caller can supply the one it already has — for the product this is
`Deformation.Examples.exists_ringEquiv_henselization_iInf_pi_henselizedLocalRing`.

## Main definitions

* `Deformation.Examples.basedIsoOfFiberEquiv` is the recognition principle the comparisons are
  built from: a family of ring isomorphisms of the fibres, linear over the Artinian base,
  compatible with the reduction to the special fibre and natural in morphisms of deformations, is
  an isomorphism of based functors.

## Main results

* `Deformation.Examples.exists_ringEquiv_henselizedLocalizationFiber`: henselizing the fibre of a
  deformation along `𝔪` is henselizing the local ring of the fibre at the inverse image of `𝔪`.
* `Deformation.Examples.exists_ringEquiv_henselizedLocalizationFamilyFiber`: the same for a finite
  family of distinct maximal ideals and their intersection, the target being the product.
* `Deformation.Examples.nonempty_basedIso_henselizationPi`: **the comparison the proof of Stacks
  0DZF uses.** Henselizing along `J = 𝔪 1 ∩ … ∩ 𝔪 n` and transporting along
  `P^h_J ≅ ∏ P^h_{𝔪 i}` is isomorphic, over `𝒞_Λ`, to localizing at each `𝔪 i`, henselizing each
  local ring, and taking the product.
* `Deformation.Examples.nonempty_basedIso_henselizationLocalization`: its one-prime case,
  henselizing at `𝔪` versus localizing at `𝔪` and then henselizing.
* `Deformation.Examples.exists_ringEquiv_henselization_of_ringEquiv`: a ring isomorphism carrying
  one ideal to another lifts to the henselizations of the two pairs.
* `Deformation.Examples.exists_ringEquiv_henselization_isLocalization_atMaximalIdeal`: the
  henselization at a maximal ideal is the henselization of *any* localization at it, not only of
  the model `Localization 𝔫ᶜ`.
* `Deformation.Examples.nonempty_basedIso_henselizationFunctor_congr`: henselization is compatible
  with transport along an isomorphism of the algebras being henselized.

## Implementation notes

The fibre of a henselized deformation is not definitionally the henselization of the fibre:
`Deformation.Examples.henselizationFunctor` is a choice of a
`Deformation.Examples.HenselizationFunctorData`, so the only handle on its value is that
structure's fields. Every computation below therefore goes through
`Deformation.Examples.HenselizationFunctorData.henselizationEquiv` and its compatibility
`henselizationEquiv_algebraMap` rather than through definitional unfolding, and every map out of
the fibre is compared by the universal property `henselization_ringHom_ext` after precomposition
with that identification.

For the same reason the Artinian base of a henselized deformation is not definitionally the base
it came from; it is identified by `CategoryTheory.BasedFunctor.w_obj`. The resulting `eqToHom`
bookkeeping is isolated in the first section, where it is discharged by proof irrelevance: two
proofs of one equality of objects give the same `eqToHom`.

`Deformation.Examples.henselizationAlgebra` is made a local instance *of priority 100*, as in
`StacksFrontier.Deformation.Examples.Geometric.IsolatedSingularities`. It has to be available, since
the deformation category of a henselization is what every statement here is about; and it has to
have low priority, since at `k = P` it also produces an `Algebra R (henselization R I)`
competing with the one carried by the `CommAlgCat` object, which is the canonical one and must
win. The low priority plays the role of an `attribute [-instance]` on the competing instance.

## References

* [Stacks Project, Tag 0DZF](https://stacks.math.columbia.edu/tag/0DZF)
* [Stacks Project, Tag 0DZD](https://stacks.math.columbia.edu/tag/0DZD)
* [Stacks Project, Tag 0DYT](https://stacks.math.columbia.edu/tag/0DYT)
* [Stacks Project, Tag 0DYS](https://stacks.math.columbia.edu/tag/0DYS)
-/

@[expose] public section

open CategoryTheory

universe u w v₁ u₁

namespace Deformation.Examples

variable {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]

attribute [local instance 100] henselizationAlgebra

/-! ### Transporting elements of Artinian bases along an equality of objects -/

/-- The underlying map of `CategoryTheory.eqToHom` on an equality of objects of `𝒞_Λ` is the
corresponding `cast`. -/
public theorem eqToHom_hom_apply {A B : ArtinianLocalAlgCat.{u, w, w} Λ k} (h : A = B) (a : A) :
    (eqToHom h).hom a = cast (congrArg ArtinianLocalAlgCat.carrier h) a := by
  subst h
  rfl

/-- Casting back along an equality of objects of `𝒞_Λ` undoes the transport along it. -/
public theorem cast_symm_eqToHom_hom {A B : ArtinianLocalAlgCat.{u, w, w} Λ k} (h : A = B)
    (a : A) :
    cast (congrArg ArtinianLocalAlgCat.carrier h.symm) ((eqToHom h).hom a) = a := by
  subst h
  rfl

/-- Transport along two equalities of objects of `𝒞_Λ` is transport along their composite. -/
public theorem eqToHom_hom_trans {A B C : ArtinianLocalAlgCat.{u, w, w} Λ k} (h₁ : A = B)
    (h₂ : B = C) (a : A) :
    (eqToHom h₂).hom ((eqToHom h₁).hom a) = (eqToHom (h₁.trans h₂)).hom a := by
  subst h₁
  subst h₂
  rfl

/-- Transport along an equality of an object of `𝒞_Λ` with itself is the identity: the equality is
a proof of a proposition, hence is `rfl`. -/
public theorem eqToHom_hom_refl {A : ArtinianLocalAlgCat.{u, w, w} Λ k} (h : A = A) (a : A) :
    (eqToHom h).hom a = a := by
  rw [eqToHom_refl]
  rfl

/-- Transport along three equalities of objects of `𝒞_Λ` is transport along any proof of the
composite equality. -/
public theorem eqToHom_hom_trans₂ {A B C D : ArtinianLocalAlgCat.{u, w, w} Λ k}
    (h₁ : A = B) (h₂ : B = C) (h₃ : C = D) (h : A = D) (a : A) :
    (eqToHom h₃).hom ((eqToHom h₂).hom ((eqToHom h₁).hom a)) = (eqToHom h).hom a := by
  subst h₁
  subst h₂
  subst h₃
  exact (eqToHom_hom_refl h a).symm

/-- Transport along two equalities of objects of `𝒞_Λ` is transport along any proof of the
composite equality. -/
public theorem eqToHom_hom_trans₁ {A B C : ArtinianLocalAlgCat.{u, w, w} Λ k}
    (h₁ : A = B) (h₂ : B = C) (h : A = C) (a : A) :
    (eqToHom h₂).hom ((eqToHom h₁).hom a) = (eqToHom h).hom a := by
  subst h₁
  subst h₂
  exact (eqToHom_hom_refl h a).symm

/-- Transport along four equalities of objects of `𝒞_Λ` is transport along any proof of the
composite equality. -/
public theorem eqToHom_hom_trans₃ {A₀ A₁ A₂ A₃ A₄ : ArtinianLocalAlgCat.{u, w, w} Λ k}
    (h₁ : A₀ = A₁) (h₂ : A₁ = A₂) (h₃ : A₂ = A₃) (h₄ : A₃ = A₄) (h : A₀ = A₄) (a : A₀) :
    (eqToHom h₄).hom ((eqToHom h₃).hom ((eqToHom h₂).hom ((eqToHom h₁).hom a))) =
      (eqToHom h).hom a := by
  subst h₁
  subst h₂
  subst h₃
  subst h₄
  exact (eqToHom_hom_refl h a).symm

/-! ### Recognising two based functors into a deformation category as isomorphic -/

section Recognition

variable {R : Type w} [CommRing R] [Algebra k R]
  {𝓕 : BasedCategory.{v₁, u₁} (ArtinianLocalAlgCat.{u, w, w} Λ k)}

/-- The Artinian bases of the two values at one object of two based functors into the deformation
category of `R` agree, both being the base of the object itself. -/
public theorem basedFunctor_base_eq
    (F G : BasedFunctor 𝓕 (ringDeformationBasedCategory Λ k R)) (X : 𝓕.obj) :
    (ringDeformationBasedCategory Λ k R).p.obj (F.obj X) =
      (ringDeformationBasedCategory Λ k R).p.obj (G.obj X) :=
  (F.w_obj X).trans (G.w_obj X).symm

/-- The identifications of `Deformation.Examples.basedFunctor_base_eq` are natural: both based
functors induce, on Artinian bases, the map induced by the source category. -/
public theorem basedFunctor_base_eq_naturality
    (F G : BasedFunctor 𝓕 (ringDeformationBasedCategory Λ k R)) {X Y : 𝓕.obj} (f : X ⟶ Y) :
    (ringDeformationBasedCategory Λ k R).p.map (F.map f) ≫
        eqToHom (basedFunctor_base_eq F G Y) =
      eqToHom (basedFunctor_base_eq F G X) ≫
        (ringDeformationBasedCategory Λ k R).p.map (G.map f) := by
  have h : (ringDeformationBasedCategory Λ k R).p.map (F.map f) =
      eqToHom (basedFunctor_base_eq F G X) ≫
        (ringDeformationBasedCategory Λ k R).p.map (G.map f) ≫
          eqToHom (basedFunctor_base_eq F G Y).symm :=
    Functor.congr_hom (F.w.trans G.w.symm) f
  rw [h]
  simp

/-- The base component of the isomorphism of deformations built from a ring isomorphism of the
fibres is the transport along the equality of bases. -/
public theorem deformationIsoOfRingEquiv_hom_left_base
    (X Y : ringDeformationCategory (Λ := Λ) (k := k) R)
    (hbase : X.left.base = Y.left.base) (e : X.left.fiber ≃+* Y.left.fiber)
    (he : ∀ a, e (algebraMap X.left.base X.left.fiber a) =
      algebraMap Y.left.base Y.left.fiber ((eqToHom hbase).hom a))
    (hs : ∀ x, Y.hom.map.hom (e x) = X.hom.map.hom x) :
    (deformationIsoOfRingEquiv X Y hbase e he hs).hom.left.base = eqToHom hbase :=
  rfl

/-- The fibre component of the isomorphism of deformations built from a ring isomorphism of the
fibres is that ring isomorphism. -/
public theorem deformationIsoOfRingEquiv_hom_left_map_hom
    (X Y : ringDeformationCategory (Λ := Λ) (k := k) R)
    (hbase : X.left.base = Y.left.base) (e : X.left.fiber ≃+* Y.left.fiber)
    (he : ∀ a, e (algebraMap X.left.base X.left.fiber a) =
      algebraMap Y.left.base Y.left.fiber ((eqToHom hbase).hom a))
    (hs : ∀ x, Y.hom.map.hom (e x) = X.hom.map.hom x) (x : X.left.fiber) :
    (deformationIsoOfRingEquiv X Y hbase e he hs).hom.left.map.hom x = e x :=
  rfl

/-- **Two based functors into the deformation category of `R` are isomorphic as soon as their
values have isomorphic fibres, compatibly.** The data required of the family of ring isomorphisms
is exactly what `Deformation.Examples.deformationIsoOfRingEquiv` needs at each object, together
with naturality in morphisms; the resulting natural isomorphism is vertical because its component
on Artinian bases is a transport along an equality. -/
public noncomputable def basedIsoOfFiberEquiv
    (F G : BasedFunctor 𝓕 (ringDeformationBasedCategory Λ k R))
    (E : ∀ X : 𝓕.obj, (F.obj X).left.fiber ≃+* (G.obj X).left.fiber)
    (hscalar : ∀ (X : 𝓕.obj) (a : (F.obj X).left.base),
      E X (algebraMap (F.obj X).left.base (F.obj X).left.fiber a) =
        algebraMap (G.obj X).left.base (G.obj X).left.fiber
          ((eqToHom (basedFunctor_base_eq F G X)).hom a))
    (hspecial : ∀ (X : 𝓕.obj) (x : (F.obj X).left.fiber),
      (G.obj X).hom.map.hom (E X x) = (F.obj X).hom.map.hom x)
    (hnat : ∀ (X Y : 𝓕.obj) (f : X ⟶ Y) (x : (F.obj X).left.fiber),
      E Y ((F.map f).left.map.hom x) = (G.map f).left.map.hom (E X x)) :
    F ≅ G := by
  refine BasedNatIso.mkNatIso (NatIso.ofComponents
    (fun X => deformationIsoOfRingEquiv (F.obj X) (G.obj X) (basedFunctor_base_eq F G X)
      (E X) (hscalar X) (hspecial X)) ?_) ?_
  · intro X Y f
    apply Over.OverMorphism.ext
    apply FlatAlgebraCategory.Hom.ext
    · exact basedFunctor_base_eq_naturality F G f
    · ext x
      exact hnat X Y f x
  · intro X
    refine IsHomLift.of_fac' _ (𝟙 (𝓕.p.obj X)) _ (F.w_obj X) (G.w_obj X) ?_
    change eqToHom (basedFunctor_base_eq F G X) =
      eqToHom (F.w_obj X) ≫ 𝟙 (𝓕.p.obj X) ≫ eqToHom (G.w_obj X).symm
    simp only [Category.id_comp, eqToHom_trans]

end Recognition

/-! ### The structural maps of the three functors being compared -/

section StructuralMaps

variable {P : Type w} [CommRing P] [Algebra k P]

/-- The structural map from the Artinian base of a henselized deformation is the henselization map
applied to the structural map of the deformation it came from. -/
public theorem HenselizationFunctorData.algebraMap_base {J : Ideal P}
    (H : HenselizationFunctorData (Λ := Λ) (k := k) J)
    (X : ringDeformationCategory (Λ := Λ) (k := k) P)
    (a : (H.functor.obj X).left.base) :
    algebraMap (H.functor.obj X).left.base (H.functor.obj X).left.fiber a =
      H.henselizationMap X
        (algebraMap X.left.base X.left.fiber ((eqToHom (H.functor.w_obj X)).hom a)) :=
  (congrArg (algebraMap _ _) (cast_symm_eqToHom_hom _ a)).symm.trans
    (H.base_comm X ((eqToHom (H.functor.w_obj X)).hom a)).symm

/-- The structural map from the Artinian base of a localized deformation is the localization map
applied to the structural map of the deformation it came from. -/
public theorem LocalizationFunctorData.algebraMap_base {S : Submonoid P}
    (L : LocalizationFunctorData (Λ := Λ) (k := k) S)
    (X : ringDeformationCategory (Λ := Λ) (k := k) P)
    (a : (L.functor.obj X).left.base) :
    algebraMap (L.functor.obj X).left.base (L.functor.obj X).left.fiber a =
      L.localizationMap X
        (algebraMap X.left.base X.left.fiber ((eqToHom (L.functor.w_obj X)).hom a)) :=
  (congrArg (algebraMap _ _) (cast_symm_eqToHom_hom _ a)).symm.trans
    (L.base_comm X ((eqToHom (L.functor.w_obj X)).hom a)).symm

/-- The inverse of the identification of the fibre of a henselized deformation sends the
henselization map to the structure map of the henselization of the fibre. -/
private theorem HenselizationFunctorData.henselizationEquiv_symm_henselizationMap {J : Ideal P}
    (H : HenselizationFunctorData (Λ := Λ) (k := k) J)
    (X : ringDeformationCategory (Λ := Λ) (k := k) P) (x : X.left.fiber) :
    (H.henselizationEquiv X).symm (H.henselizationMap X x) =
      algebraMap X.left.fiber (henselization X.left.fiber (J.comap X.hom.map.hom) : Type w) x :=
  (H.henselizationEquiv X).symm_apply_eq.mpr (H.henselizationEquiv_algebraMap X x).symm

/-- Two ring maps out of a ring `F ≅ A^h_I` into (a copy of) a henselian pair agree if they agree on
the image of `A` and carry the image of `I` into the henselian ideal. -/
private theorem eq_of_henselization_equiv {A F T T' : Type w} [CommRing A] [CommRing F]
    [CommRing T] [CommRing T'] {I : Ideal A} (φ : (henselization A I : Type w) ≃+* F)
    (ι : A →+* F) (hι : ∀ a, φ (algebraMap A (henselization A I : Type w) a) = ι a)
    (ψ : T ≃+* T') (N : Ideal T') (hT : HenselianPair T' N) (u v : F →+* T)
    (hu : ∀ a, u (ι a) = v (ι a)) (hmem : ∀ a ∈ I, ψ (u (ι a)) ∈ N) (x : F) : u x = v x := by
  obtain ⟨y, rfl⟩ := φ.surjective x
  refine ψ.injective (DFunLike.congr_fun (henselization_ringHom_ext I N hT
    (ψ.toRingHom.comp (u.comp φ.toRingHom)) (ψ.toRingHom.comp (v.comp φ.toRingHom))
    (fun a ha => ?_) (RingHom.ext fun a => ?_)) y)
  · change ψ (u (φ (algebraMap A _ a))) ∈ N
    rw [hι]
    exact hmem a ha
  · change ψ (u (φ (algebraMap A _ a))) = ψ (v (φ (algebraMap A _ a)))
    rw [hι, hu]

variable {ι : Type w} [Finite ι]

/-- The reduction to the special fibre of a product of deformations is, in each component, the
reduction of that component. -/
public theorem piDeformation_specialFiber_apply
    (R : ι → Type w) [∀ i, CommRing (R i)] [∀ i, Algebra k (R i)]
    (A : ArtinianLocalAlgCat.{u, w, w} Λ k)
    (Z : ∀ i, (ringDeformationBasedCategory Λ k (R i)).p.Fiber A)
    (x : (piDeformation R A Z).left.fiber) (i : ι) :
    (piDeformation R A Z).hom.map.hom x i = (Z i).val.hom.map.hom (x i) :=
  rfl

end StructuralMaps

/-! ### The structural maps of a transport along a ring isomorphism -/

section Transport

variable {R S : Type w} [CommRing R] [Algebra k R] [CommRing S] [Algebra k S]
  (e : R ≃+* S) (he : ∀ a : k, e (algebraMap k R a) = algebraMap k S a)

/-- The reduction to the special fibre of a transported deformation is the reduction of the
original composed with the ring isomorphism. -/
public theorem ringDeformationTransport_specialFiber_apply
    (X : ringDeformationCategory (Λ := Λ) (k := k) R) (x : X.left.fiber) :
    ((ringDeformationTransport (Λ := Λ) e he).obj X).hom.map.hom x = e (X.hom.map.hom x) :=
  rfl

end Transport

/-! ### Transporting a henselization along a ring isomorphism -/

/-- **A ring isomorphism carrying one ideal to another lifts to the henselizations of the two
pairs.** Both directions are produced by the universal property of the henselization, and the two
composites are the respective identities by its uniqueness clause. -/
public theorem exists_ringEquiv_henselization_of_ringEquiv
    {R S : Type w} [CommRing R] [CommRing S]
    (e : R ≃+* S) (I : Ideal R) (J : Ideal S) (he : I.map e.toRingHom = J) :
    ∃ a : (henselization R I : Type w) ≃+* (henselization S J : Type w),
      ∀ r, a (algebraMap R (henselization R I : Type w) r) =
        algebraMap S (henselization S J : Type w) (e r) := by
  let H := (henselization R I : Type w)
  let K := (henselization S J : Type w)
  let N := I.map (algebraMap R H)
  let M := J.map (algebraMap S K)
  have hI : I ≤ M.comap ((algebraMap S K).comp e.toRingHom) := by
    rw [← Ideal.map_le_iff_le_comap, ← Ideal.map_map, he]
  have hJ : J ≤ N.comap ((algebraMap R H).comp e.symm.toRingHom) := by
    rw [← he, Ideal.map_le_iff_le_comap, Ideal.comap_comap]
    intro x hx
    change algebraMap R H (e.symm (e x)) ∈ N
    rw [e.symm_apply_apply]
    exact Ideal.mem_map_of_mem _ hx
  obtain ⟨f, hf, -⟩ := henselization_universalProperty R I K inferInstance M
    (henselianPair_henselization S J) ((algebraMap S K).comp e.toRingHom) hI
  obtain ⟨g, hg, -⟩ := henselization_universalProperty S J H inferInstance N
    (henselianPair_henselization R I) ((algebraMap R H).comp e.symm.toRingHom) hJ
  have hgf : g.comp f = RingHom.id H := by
    have heq : (g.comp f).comp (algebraMap R H) = algebraMap R H := by
      ext r
      change g (f (algebraMap R H r)) = _
      rw [show f (algebraMap R H r) = algebraMap S K (e r) from DFunLike.congr_fun hf.1 r,
        show g (algebraMap S K (e r)) = algebraMap R H (e.symm (e r)) from
          DFunLike.congr_fun hg.1 (e r)]
      exact congrArg (algebraMap R H) (e.symm_apply_apply r)
    apply henselization_ringHom_ext I N (henselianPair_henselization R I)
    · rw [heq]
      exact Ideal.le_comap_map
    · simpa using heq
  have hfg : f.comp g = RingHom.id K := by
    have heq : (f.comp g).comp (algebraMap S K) = algebraMap S K := by
      ext r
      change f (g (algebraMap S K r)) = _
      rw [show g (algebraMap S K r) = algebraMap R H (e.symm r) from DFunLike.congr_fun hg.1 r,
        show f (algebraMap R H (e.symm r)) = algebraMap S K (e (e.symm r)) from
          DFunLike.congr_fun hf.1 (e.symm r)]
      exact congrArg (algebraMap S K) (e.apply_symm_apply r)
    apply henselization_ringHom_ext J M (henselianPair_henselization S J)
    · rw [heq]
      exact Ideal.le_comap_map
    · simpa using heq
  exact ⟨RingEquiv.ofRingHom f g hfg hgf, fun r => DFunLike.congr_fun hf.1 r⟩

/-! ### Henselizing an abstract localization at a maximal ideal -/

/-- **The henselization of `(R, 𝔫)` at a maximal ideal `𝔫` is the henselization of any
localization of `R` at `𝔫`, along its maximal ideal.** This is
`exists_ringEquiv_henselization_localization_atMaximalIdeal` read at an arbitrary localization
rather than at the model `Localization 𝔫ᶜ`, which is what lets it be applied to the fibre of a
localized deformation: that fibre is a localization of the fibre of the original deformation by
`Deformation.Examples.LocalizationFunctorData.isLocalization`, but it is not the model one. The
two localizations are identified by `IsLocalization.algEquiv` and the identification is carried to
the henselizations by `Deformation.Examples.exists_ringEquiv_henselization_of_ringEquiv`. -/
public theorem exists_ringEquiv_henselization_isLocalization_atMaximalIdeal
    {R : Type w} [CommRing R] (n : Ideal R) [n.IsMaximal]
    (A : Type w) [CommRing A] [Algebra R A] [IsLocalization n.primeCompl A] [IsLocalRing A] :
    ∃ e : (henselization R n : Type w) ≃+*
        (henselization A (IsLocalRing.maximalIdeal A) : Type w),
      ∀ r : R, e (algebraMap R (henselization R n : Type w) r) =
        algebraMap A (henselization A (IsLocalRing.maximalIdeal A) : Type w)
          (algebraMap R A r) := by
  classical
  obtain ⟨c, hc⟩ := exists_ringEquiv_henselization_localization_atMaximalIdeal n
  let φ : Localization n.primeCompl ≃+* A :=
    (IsLocalization.algEquiv n.primeCompl (Localization n.primeCompl) A).toRingEquiv
  have hφ : ∀ r : R, φ (algebraMap R (Localization n.primeCompl) r) = algebraMap R A r :=
    fun r => (IsLocalization.algEquiv n.primeCompl (Localization n.primeCompl) A).commutes r
  have hmax : ((IsLocalRing.maximalIdeal
      (Localization n.primeCompl)).map φ.toRingHom).IsMaximal :=
    (Ideal.isMaximal_map_iff_of_bijective φ.toRingHom φ.bijective).mpr
      (IsLocalRing.maximalIdeal.isMaximal (Localization n.primeCompl))
  have hmap : (IsLocalRing.maximalIdeal (Localization n.primeCompl)).map φ.toRingHom =
      IsLocalRing.maximalIdeal A :=
    IsLocalRing.eq_maximalIdeal hmax
  obtain ⟨d, hd⟩ := exists_ringEquiv_henselization_of_ringEquiv φ
    (IsLocalRing.maximalIdeal (Localization n.primeCompl)) (IsLocalRing.maximalIdeal A) hmap
  refine ⟨c.trans d, fun r => ?_⟩
  change d (c (algebraMap R (henselization R n : Type w) r)) = _
  rw [hc r, hd, hφ]


/-! ### Henselizing a deformation at a maximal ideal -/

section Fiber

variable {P : Type w} [CommRing P] [Algebra k P]

/-- **Henselizing a deformation along a maximal ideal `𝔪` of `P` is localizing it at `𝔪` and then
henselizing.** On the level of a single deformation `X` this is the statement that the
henselization of the pair `(Q, 𝔪 Q)`, for `Q` the fibre of `X`, is the henselization of the local
ring of `Q` at `𝔪 Q`; the inverse image `𝔪 Q` is again maximal because the reduction of a
deformation to its special fibre is surjective. -/
public theorem exists_ringEquiv_henselizedLocalizationFiber
    (m : Ideal P) [m.IsMaximal] (X : ringDeformationCategory (Λ := Λ) (k := k) P) :
    ∃ e : ((henselizationFunctor (Λ := Λ) (k := k) m).functor.obj X).left.fiber ≃+*
        ((henselizationFunctor (Λ := Λ) (k := k)
            (IsLocalRing.maximalIdeal (Localization m.primeCompl))).functor.obj
          ((localizationFunctor (Λ := Λ) (k := k) m.primeCompl).functor.obj X)).left.fiber,
      ∀ x, e ((henselizationFunctor (Λ := Λ) (k := k) m).henselizationMap X x) =
        (henselizationFunctor (Λ := Λ) (k := k)
            (IsLocalRing.maximalIdeal (Localization m.primeCompl))).henselizationMap
          ((localizationFunctor (Λ := Λ) (k := k) m.primeCompl).functor.obj X)
          ((localizationFunctor (Λ := Λ) (k := k) m.primeCompl).localizationMap X x) := by
  classical
  let H := henselizationFunctor (Λ := Λ) (k := k) m
  let L := localizationFunctor (Λ := Λ) (k := k) m.primeCompl
  let K' := henselizationFunctor (Λ := Λ) (k := k)
    (IsLocalRing.maximalIdeal (Localization m.primeCompl))
  let Y := L.functor.obj X
  let n : Ideal X.left.fiber := m.comap X.hom.map.hom
  let hn : n.IsMaximal :=
    Ideal.comap_isMaximal_of_surjective X.hom.map.hom
      (deformationSpecialFiberMap_surjective X) (K := m) (H := ‹m.IsMaximal›)
  let : Algebra X.left.fiber Y.left.fiber := (L.localizationMap X).toAlgebra
  have halg : ∀ y : X.left.fiber,
      algebraMap X.left.fiber Y.left.fiber y = L.localizationMap X y := fun _ => rfl
  let : IsLocalization n.primeCompl Y.left.fiber := L.isLocalization X
  let : IsLocalRing Y.left.fiber := IsLocalization.AtPrime.isLocalRing Y.left.fiber n
  let hMY : ((IsLocalRing.maximalIdeal (Localization m.primeCompl)).comap
      Y.hom.map.hom).IsMaximal :=
    Ideal.comap_isMaximal_of_surjective Y.hom.map.hom
      (deformationSpecialFiberMap_surjective Y)
      (K := IsLocalRing.maximalIdeal (Localization m.primeCompl))
      (H := IsLocalRing.maximalIdeal.isMaximal (Localization m.primeCompl))
  have hM : IsLocalRing.maximalIdeal Y.left.fiber =
      (IsLocalRing.maximalIdeal (Localization m.primeCompl)).comap Y.hom.map.hom :=
    (IsLocalRing.eq_maximalIdeal hMY).symm
  obtain ⟨c, hc⟩ :=
    exists_ringEquiv_henselization_isLocalization_atMaximalIdeal n Y.left.fiber
  let d := henselizationEquivOfIdealEq (IsLocalRing.maximalIdeal Y.left.fiber)
    ((IsLocalRing.maximalIdeal (Localization m.primeCompl)).comap Y.hom.map.hom) hM
  refine ⟨(H.henselizationEquiv X).symm.trans
    (c.trans (d.val.trans (K'.henselizationEquiv Y))), fun x => ?_⟩
  change K'.henselizationEquiv Y (d.val (c ((H.henselizationEquiv X).symm
    (H.henselizationMap X x)))) = K'.henselizationMap Y (L.localizationMap X x)
  have e1 := H.henselizationEquiv_symm_henselizationMap X x
  have e2 : c (algebraMap X.left.fiber (henselization X.left.fiber n : Type w) x) =
      algebraMap Y.left.fiber
        (henselization Y.left.fiber (IsLocalRing.maximalIdeal Y.left.fiber) : Type w)
        (algebraMap X.left.fiber Y.left.fiber x) :=
    hc x
  have e3 : d.val (algebraMap Y.left.fiber
        (henselization Y.left.fiber (IsLocalRing.maximalIdeal Y.left.fiber) : Type w)
        (algebraMap X.left.fiber Y.left.fiber x)) =
      algebraMap Y.left.fiber (henselization Y.left.fiber
        ((IsLocalRing.maximalIdeal (Localization m.primeCompl)).comap
          Y.hom.map.hom) : Type w) (algebraMap X.left.fiber Y.left.fiber x) :=
    d.property (algebraMap X.left.fiber Y.left.fiber x)
  rw [e1, e2, e3, halg]
  exact K'.henselizationEquiv_algebraMap Y (L.localizationMap X x)

/-- **Henselizing a deformation along a finite intersection of distinct maximal ideals is
localizing it at each of them, henselizing, and taking the product.** This is
`Deformation.Examples.exists_ringEquiv_henselizedLocalizationFiber` for a family, combined with
the decomposition of a henselization at a finite intersection of distinct maximal ideals as a
product of henselizations of local rings. -/
public theorem exists_ringEquiv_henselizedLocalizationFamilyFiber
    {ι : Type w} [Finite ι] (m : ι → PrimeSpectrum P)
    (hmax : ∀ i, (m i).asIdeal.IsMaximal) (hinj : Function.Injective m)
    (X : ringDeformationCategory (Λ := Λ) (k := k) P) :
    ∃ e : ((henselizationFunctor (Λ := Λ) (k := k)
          (⨅ i, (m i).asIdeal)).functor.obj X).left.fiber ≃+*
        (∀ i, ((henselizationFunctor (Λ := Λ) (k := k)
            (IsLocalRing.maximalIdeal (localRingAt (m i)))).functor.obj
          ((localizationFunctor (Λ := Λ) (k := k)
            (m i).asIdeal.primeCompl).functor.obj X)).left.fiber),
      ∀ x i, e ((henselizationFunctor (Λ := Λ) (k := k)
            (⨅ j, (m j).asIdeal)).henselizationMap X x) i =
        (henselizationFunctor (Λ := Λ) (k := k)
            (IsLocalRing.maximalIdeal (localRingAt (m i)))).henselizationMap
          ((localizationFunctor (Λ := Λ) (k := k) (m i).asIdeal.primeCompl).functor.obj X)
          ((localizationFunctor (Λ := Λ) (k := k)
            (m i).asIdeal.primeCompl).localizationMap X x) := by
  classical
  have hsurj : Function.Surjective X.hom.map.hom := deformationSpecialFiberMap_surjective X
  let q : ι → Ideal X.left.fiber := fun i => (m i).asIdeal.comap X.hom.map.hom
  have hqmax : ∀ i, (q i).IsMaximal := fun i =>
    Ideal.comap_isMaximal_of_surjective X.hom.map.hom hsurj
      (K := (m i).asIdeal) (H := hmax i)
  let : ∀ i, (q i).IsMaximal := hqmax
  have hqinj : Function.Injective q := by
    intro i j hij
    have hij' : (m i).asIdeal.comap X.hom.map.hom =
      (m j).asIdeal.comap X.hom.map.hom := hij
    exact hinj (PrimeSpectrum.ext
      (Ideal.comap_injective_of_surjective X.hom.map.hom hsurj hij'))
  obtain ⟨eQ, heQ⟩ := exists_ringEquiv_henselization_iInf_pi_localization q hqmax hqinj
  have hJ : (⨅ i, (m i).asIdeal).comap X.hom.map.hom = ⨅ i, q i := Ideal.comap_iInf _ _
  let eJ := henselizationEquivOfIdealEq ((⨅ i, (m i).asIdeal).comap X.hom.map.hom)
    (⨅ i, q i) hJ
  let H := henselizationFunctor (Λ := Λ) (k := k) (⨅ i, (m i).asIdeal)
  let L := fun i => localizationFunctor (Λ := Λ) (k := k) (m i).asIdeal.primeCompl
  let K' := fun i =>
    henselizationFunctor (Λ := Λ) (k := k) (IsLocalRing.maximalIdeal (localRingAt (m i)))
  have hcomponent : ∀ i, ∃ c : (henselization (Localization (q i).primeCompl)
        (IsLocalRing.maximalIdeal (Localization (q i).primeCompl)) : Type w) ≃+*
      ((K' i).functor.obj ((L i).functor.obj X)).left.fiber,
      ∀ x, c (algebraMap (Localization (q i).primeCompl)
          (henselization (Localization (q i).primeCompl)
            (IsLocalRing.maximalIdeal (Localization (q i).primeCompl)) : Type w)
          (algebraMap X.left.fiber (Localization (q i).primeCompl) x)) =
        (K' i).henselizationMap ((L i).functor.obj X) ((L i).localizationMap X x) := by
    intro i
    let := hmax i
    obtain ⟨a, ha⟩ := exists_ringEquiv_henselization_localization_atMaximalIdeal (q i)
    obtain ⟨b, hb⟩ := exists_ringEquiv_henselizedLocalizationFiber (m i).asIdeal X
    let Hi := henselizationFunctor (Λ := Λ) (k := k) (m i).asIdeal
    refine ⟨a.symm.trans ((Hi.henselizationEquiv X).trans b), fun x => ?_⟩
    change b (Hi.henselizationEquiv X (a.symm (algebraMap (Localization (q i).primeCompl)
      (henselization (Localization (q i).primeCompl)
        (IsLocalRing.maximalIdeal (Localization (q i).primeCompl)) : Type w)
      (algebraMap X.left.fiber (Localization (q i).primeCompl) x)))) = _
    have e1 : a.symm (algebraMap (Localization (q i).primeCompl)
        (henselization (Localization (q i).primeCompl)
          (IsLocalRing.maximalIdeal (Localization (q i).primeCompl)) : Type w)
        (algebraMap X.left.fiber (Localization (q i).primeCompl) x)) =
        algebraMap X.left.fiber (henselization X.left.fiber (q i) : Type w) x :=
      a.symm_apply_eq.mpr (ha x).symm
    have e2 : Hi.henselizationEquiv X
        (algebraMap X.left.fiber (henselization X.left.fiber (q i) : Type w) x) =
        Hi.henselizationMap X x :=
      Hi.henselizationEquiv_algebraMap X x
    rw [e1, e2]
    exact hb x
  choose E hE using hcomponent
  refine ⟨(H.henselizationEquiv X).symm.trans
    (eJ.val.trans (eQ.trans (RingEquiv.piCongrRight E))), fun x i => ?_⟩
  change E i (eQ (eJ.val ((H.henselizationEquiv X).symm (H.henselizationMap X x))) i) =
    (K' i).henselizationMap ((L i).functor.obj X) ((L i).localizationMap X x)
  have e1 := H.henselizationEquiv_symm_henselizationMap X x
  have e2 : eJ.val (algebraMap X.left.fiber
        (henselization X.left.fiber ((⨅ i, (m i).asIdeal).comap X.hom.map.hom) : Type w) x) =
      algebraMap X.left.fiber (henselization X.left.fiber (⨅ i, q i) : Type w) x :=
    eJ.property x
  have e3 : eQ (algebraMap X.left.fiber
        (henselization X.left.fiber (⨅ i, q i) : Type w) x) i =
      algebraMap (Localization (q i).primeCompl)
        (henselization (Localization (q i).primeCompl)
          (IsLocalRing.maximalIdeal (Localization (q i).primeCompl)) : Type w)
        (algebraMap X.left.fiber (Localization (q i).primeCompl) x) :=
    heQ x i
  rw [e1, e2, e3]
  exact hE i x

end Fiber

/-! ### The comparison at a single maximal ideal -/

section SingleComparison

variable {P : Type w} [CommRing P] [Algebra k P] (m : Ideal P) [m.IsMaximal]
  (H : HenselizationFunctorData (Λ := Λ) (k := k) m)
  (L : LocalizationFunctorData (Λ := Λ) (k := k) m.primeCompl)
  (K' : HenselizationFunctorData (Λ := Λ) (k := k)
    (IsLocalRing.maximalIdeal (Localization m.primeCompl)))
  (E : ∀ X : ringDeformationCategory (Λ := Λ) (k := k) P,
    (H.functor.obj X).left.fiber ≃+* (K'.functor.obj (L.functor.obj X)).left.fiber)
  (hE : ∀ (X : ringDeformationCategory (Λ := Λ) (k := k) P) (x : X.left.fiber),
    E X (H.henselizationMap X x) =
      K'.henselizationMap (L.functor.obj X) (L.localizationMap X x))

/-- The isomorphism `P^h_𝔪 ≅ (P_𝔪)^h` is `k`-linear: both sides are `k`-algebras through `P`, and
the isomorphism is compatible with the maps out of `P`. -/
public theorem algebraMap_comm_of_henselizationLocalizationEquiv
    (e : (henselization P m : Type w) ≃+*
      (henselization (Localization m.primeCompl)
        (IsLocalRing.maximalIdeal (Localization m.primeCompl)) : Type w))
    (hchar : ∀ r : P, e (algebraMap P (henselization P m : Type w) r) =
      algebraMap (Localization m.primeCompl)
        (henselization (Localization m.primeCompl)
          (IsLocalRing.maximalIdeal (Localization m.primeCompl)) : Type w)
        (algebraMap P (Localization m.primeCompl) r)) :
    ∀ a : k, e (algebraMap k (henselization P m : Type w) a) =
      algebraMap k (henselization (Localization m.primeCompl)
        (IsLocalRing.maximalIdeal (Localization m.primeCompl)) : Type w) a := by
  intro a
  let : IsScalarTower k P (henselization P m : Type w) :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  let : IsScalarTower k (Localization m.primeCompl)
      (henselization (Localization m.primeCompl)
        (IsLocalRing.maximalIdeal (Localization m.primeCompl)) : Type w) :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  rw [IsScalarTower.algebraMap_apply k P (henselization P m : Type w), hchar,
    IsScalarTower.algebraMap_apply k (Localization m.primeCompl)
      (henselization (Localization m.primeCompl)
        (IsLocalRing.maximalIdeal (Localization m.primeCompl)) : Type w),
    IsScalarTower.algebraMap_apply k P (Localization m.primeCompl)]

include hE in
/-- **The fibre comparison is linear over the Artinian base.** Both structural maps out of the
Artinian base factor through the henselization, respectively localization, map. -/
public theorem henselizedLocalization_scalar_comm
    (X : ringDeformationCategory (Λ := Λ) (k := k) P)
    (hp : (H.functor.obj X).left.base = (K'.functor.obj (L.functor.obj X)).left.base)
    (a : (H.functor.obj X).left.base) :
    E X (algebraMap (H.functor.obj X).left.base (H.functor.obj X).left.fiber a) =
      algebraMap (K'.functor.obj (L.functor.obj X)).left.base
        (K'.functor.obj (L.functor.obj X)).left.fiber ((eqToHom hp).hom a) := by
  refine ((congrArg (E X) (H.algebraMap_base X a)).trans (hE X _)).trans ?_
  refine Eq.trans ?_ (K'.algebraMap_base (L.functor.obj X) ((eqToHom hp).hom a)).symm
  refine congrArg (K'.henselizationMap (L.functor.obj X)) ?_
  refine Eq.trans ?_ (L.algebraMap_base X _).symm
  exact congrArg (fun z => L.localizationMap X (algebraMap X.left.base X.left.fiber z))
    (eqToHom_hom_trans₂ hp (K'.functor.w_obj (L.functor.obj X)) (L.functor.w_obj X)
      (H.functor.w_obj X) a).symm

include hE in
/-- **The fibre comparison commutes with the reduction to the special fibre.** Both sides are maps
out of a henselization which agree on the ring, hence agree. -/
public theorem henselizedLocalization_specialFiber_comm
    (e : (henselization P m : Type w) ≃+*
      (henselization (Localization m.primeCompl)
        (IsLocalRing.maximalIdeal (Localization m.primeCompl)) : Type w))
    (hchar : ∀ r : P, e (algebraMap P (henselization P m : Type w) r) =
      algebraMap (Localization m.primeCompl)
        (henselization (Localization m.primeCompl)
          (IsLocalRing.maximalIdeal (Localization m.primeCompl)) : Type w)
        (algebraMap P (Localization m.primeCompl) r))
    (X : ringDeformationCategory (Λ := Λ) (k := k) P)
    (x : (H.functor.obj X).left.fiber) :
    (K'.functor.obj (L.functor.obj X)).hom.map.hom (E X x) =
      e ((H.functor.obj X).hom.map.hom x) := by
  have hval : ∀ z : X.left.fiber,
      (K'.functor.obj (L.functor.obj X)).hom.map.hom (E X (H.henselizationMap X z)) =
        algebraMap (Localization m.primeCompl)
          (henselization (Localization m.primeCompl)
            (IsLocalRing.maximalIdeal (Localization m.primeCompl)) : Type w)
          (algebraMap P (Localization m.primeCompl) (X.hom.map.hom z)) := fun z =>
    (congrArg _ (hE X z)).trans
      ((K'.specialFiber_comm (L.functor.obj X) _).trans
        (congrArg _ (L.specialFiber_comm X z).symm))
  refine eq_of_henselization_equiv (H.henselizationEquiv X) (H.henselizationMap X)
    (H.henselizationEquiv_algebraMap X) (RingEquiv.refl _)
    ((IsLocalRing.maximalIdeal (Localization m.primeCompl)).map
      (algebraMap (Localization m.primeCompl)
        (henselization (Localization m.primeCompl)
          (IsLocalRing.maximalIdeal (Localization m.primeCompl)) : Type w)))
    (henselianPair_henselization (Localization m.primeCompl)
      (IsLocalRing.maximalIdeal (Localization m.primeCompl)))
    ((K'.functor.obj (L.functor.obj X)).hom.map.hom.comp (E X).toRingHom)
    (e.toRingHom.comp (H.functor.obj X).hom.map.hom) (fun z => ?_) (fun z hz => ?_) x
  · change (K'.functor.obj (L.functor.obj X)).hom.map.hom (E X (H.henselizationMap X z)) =
      e ((H.functor.obj X).hom.map.hom (H.henselizationMap X z))
    rw [hval, H.specialFiber_comm]
    exact (hchar _).symm
  · change (K'.functor.obj (L.functor.obj X)).hom.map.hom (E X (H.henselizationMap X z)) ∈ _
    rw [hval]
    exact Ideal.mem_map_of_mem _ ((IsLocalization.AtPrime.map_eq_maximalIdeal m
      (Localization m.primeCompl)).le (Ideal.mem_map_of_mem _ (Ideal.mem_comap.mp hz)))

include hE in
/-- **The fibre comparison is natural in morphisms of deformations.** Both sides are maps out of a
henselization which agree on the ring, hence agree. -/
public theorem henselizedLocalization_naturality
    {X Y : ringDeformationCategory (Λ := Λ) (k := k) P} (f : X ⟶ Y)
    (x : (H.functor.obj X).left.fiber) :
    E Y ((H.functor.map f).left.map.hom x) =
      (K'.functor.map (L.functor.map f)).left.map.hom (E X x) := by
  refine eq_of_henselization_equiv (H.henselizationEquiv X) (H.henselizationMap X)
    (H.henselizationEquiv_algebraMap X) (K'.henselizationEquiv (L.functor.obj Y)).symm
    (((IsLocalRing.maximalIdeal (Localization m.primeCompl)).comap
      (L.functor.obj Y).hom.map.hom).map (algebraMap (L.functor.obj Y).left.fiber
        (henselization (L.functor.obj Y).left.fiber
          ((IsLocalRing.maximalIdeal (Localization m.primeCompl)).comap
            (L.functor.obj Y).hom.map.hom) : Type w)))
    (henselianPair_henselization _ _)
    ((E Y).toRingHom.comp (H.functor.map f).left.map.hom)
    ((K'.functor.map (L.functor.map f)).left.map.hom.comp (E X).toRingHom)
    (fun z => ?_) (fun z hz => ?_) x
  · change E Y ((H.functor.map f).left.map.hom (H.henselizationMap X z)) =
      (K'.functor.map (L.functor.map f)).left.map.hom (E X (H.henselizationMap X z))
    rw [← H.naturality, hE, hE]
    exact (congrArg _ (L.naturality f z)).trans (K'.naturality (L.functor.map f) _)
  · change (K'.henselizationEquiv (L.functor.obj Y)).symm
      (E Y ((H.functor.map f).left.map.hom (H.henselizationMap X z))) ∈ _
    rw [← H.naturality, hE]
    refine Eq.mpr (congrArg (· ∈ _)
      (K'.henselizationEquiv_symm_henselizationMap (L.functor.obj Y) _))
      (Ideal.mem_map_of_mem _ (Ideal.mem_comap.mpr ?_))
    have h1 : (L.functor.obj Y).hom.map.hom (L.localizationMap Y (f.left.map.hom z)) =
        algebraMap P (Localization m.primeCompl) (X.hom.map.hom z) :=
      (L.specialFiber_comm Y (f.left.map.hom z)).symm.trans
        (congrArg (algebraMap P (Localization m.primeCompl)) (deformationMorphism_map_comm f z))
    exact Eq.mpr (congrArg (· ∈ IsLocalRing.maximalIdeal (Localization m.primeCompl)) h1)
      ((IsLocalization.AtPrime.map_eq_maximalIdeal m (Localization m.primeCompl)).le
        (Ideal.mem_map_of_mem _ (Ideal.mem_comap.mp hz)))

/-- **Henselizing along a maximal ideal `𝔪` of `P` is localizing at `𝔪` and then henselizing**, as
functors of deformation categories over `𝒞_Λ`: the henselization functor of **Stacks 0DZD** at
`(P, 𝔪)`, followed by the transport along the isomorphism `P^h_𝔪 ≅ (P_𝔪)^h`, is isomorphic to the
localization functor of **Stacks 0DYS** at `𝔪` followed by the henselization functor at the
maximal ideal of `P_𝔪`.

The ring isomorphism and its compatibility with the maps out of `P` are hypotheses, not
existentials: they are exactly what
`exists_ringEquiv_henselization_localization_atMaximalIdeal` produces. -/
public theorem nonempty_basedIso_henselizationLocalization
    (e : (henselization P m : Type w) ≃+*
      (henselization (Localization m.primeCompl)
        (IsLocalRing.maximalIdeal (Localization m.primeCompl)) : Type w))
    (he : ∀ a : k, e (algebraMap k (henselization P m : Type w) a) =
      algebraMap k (henselization (Localization m.primeCompl)
        (IsLocalRing.maximalIdeal (Localization m.primeCompl)) : Type w) a)
    (hchar : ∀ r : P, e (algebraMap P (henselization P m : Type w) r) =
      algebraMap (Localization m.primeCompl)
        (henselization (Localization m.primeCompl)
          (IsLocalRing.maximalIdeal (Localization m.primeCompl)) : Type w)
        (algebraMap P (Localization m.primeCompl) r)) :
    Nonempty (BasedFunctor.comp (henselizationFunctor (Λ := Λ) (k := k) m).functor
        (ringDeformationTransport e he) ≅
      BasedFunctor.comp (localizationFunctor (Λ := Λ) (k := k) m.primeCompl).functor
        (henselizationFunctor (Λ := Λ) (k := k)
          (IsLocalRing.maximalIdeal (Localization m.primeCompl))).functor) := by
  classical
  choose E hE using fun X => exists_ringEquiv_henselizedLocalizationFiber
    (Λ := Λ) (k := k) m X
  refine ⟨basedIsoOfFiberEquiv _ _ E (fun X a => ?_) (fun X x => ?_) (fun X Y f x => ?_)⟩
  · exact henselizedLocalization_scalar_comm m _ _ _ E hE X _ a
  · exact henselizedLocalization_specialFiber_comm m _ _ _ E hE e hchar X x
  · exact henselizedLocalization_naturality m _ _ _ E hE f x

end SingleComparison

/-! ### Henselization is compatible with transport along an isomorphism of algebras -/

section CongrComparison

variable {R S : Type w} [CommRing R] [Algebra k R] [CommRing S] [Algebra k S]
  (eRS : R ≃+* S) (heRS : ∀ a : k, eRS (algebraMap k R a) = algebraMap k S a)
  (I : Ideal R) (J : Ideal S)
  (d : (henselization R I : Type w) ≃+* (henselization S J : Type w))
  (H : HenselizationFunctorData (Λ := Λ) (k := k) I)
  (K' : HenselizationFunctorData (Λ := Λ) (k := k) J)
  (E : ∀ X : ringDeformationCategory (Λ := Λ) (k := k) R,
    (H.functor.obj X).left.fiber ≃+*
      (K'.functor.obj ((ringDeformationTransport eRS heRS).obj X)).left.fiber)
  (hE : ∀ (X : ringDeformationCategory (Λ := Λ) (k := k) R) (x : X.left.fiber),
    E X (H.henselizationMap X x) =
      K'.henselizationMap ((ringDeformationTransport eRS heRS).obj X) x)

include heRS in
/-- The isomorphism of henselizations induced by an isomorphism of the algebras being henselized
is `k`-linear, because the isomorphism of algebras is. -/
public theorem algebraMap_comm_of_henselizationCongrEquiv
    (hchar : ∀ r : R, d (algebraMap R (henselization R I : Type w) r) =
      algebraMap S (henselization S J : Type w) (eRS r)) :
    ∀ a : k, d (algebraMap k (henselization R I : Type w) a) =
      algebraMap k (henselization S J : Type w) a := by
  intro a
  let : IsScalarTower k R (henselization R I : Type w) :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  let : IsScalarTower k S (henselization S J : Type w) :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  rw [IsScalarTower.algebraMap_apply k R (henselization R I : Type w), hchar, heRS,
    IsScalarTower.algebraMap_apply k S (henselization S J : Type w)]

include hE in
/-- **The fibre comparison of the congruence square is linear over the Artinian base.** -/
public theorem henselizationCongr_scalar_comm
    (X : ringDeformationCategory (Λ := Λ) (k := k) R)
    (hp : (H.functor.obj X).left.base =
      (K'.functor.obj ((ringDeformationTransport eRS heRS).obj X)).left.base)
    (a : (H.functor.obj X).left.base) :
    E X (algebraMap (H.functor.obj X).left.base (H.functor.obj X).left.fiber a) =
      algebraMap (K'.functor.obj ((ringDeformationTransport eRS heRS).obj X)).left.base
        (K'.functor.obj ((ringDeformationTransport eRS heRS).obj X)).left.fiber
        ((eqToHom hp).hom a) := by
  refine ((congrArg (E X) (H.algebraMap_base X a)).trans (hE X _)).trans ?_
  refine Eq.trans ?_ (K'.algebraMap_base ((ringDeformationTransport eRS heRS).obj X)
    ((eqToHom hp).hom a)).symm
  refine congrArg
    (K'.henselizationMap ((ringDeformationTransport eRS heRS).obj X)) ?_
  exact congrArg (algebraMap X.left.base X.left.fiber)
    (eqToHom_hom_trans₁ hp
      (K'.functor.w_obj ((ringDeformationTransport eRS heRS).obj X))
      (H.functor.w_obj X) a).symm

include hE in
/-- **The fibre comparison of the congruence square commutes with the reduction to the special
fibre.** -/
public theorem henselizationCongr_specialFiber_comm
    (hmem : ∀ r : R, r ∈ I → eRS r ∈ J)
    (hchar : ∀ r : R, d (algebraMap R (henselization R I : Type w) r) =
      algebraMap S (henselization S J : Type w) (eRS r))
    (X : ringDeformationCategory (Λ := Λ) (k := k) R)
    (x : (H.functor.obj X).left.fiber) :
    (K'.functor.obj ((ringDeformationTransport eRS heRS).obj X)).hom.map.hom (E X x) =
      d ((H.functor.obj X).hom.map.hom x) := by
  have hval : ∀ z : X.left.fiber,
      (K'.functor.obj ((ringDeformationTransport eRS heRS).obj X)).hom.map.hom
          (E X (H.henselizationMap X z)) =
        algebraMap S (henselization S J : Type w) (eRS (X.hom.map.hom z)) := fun z =>
    (congrArg _ (hE X z)).trans
      ((K'.specialFiber_comm ((ringDeformationTransport eRS heRS).obj X) z).trans
        (congrArg (algebraMap S (henselization S J : Type w))
          (ringDeformationTransport_specialFiber_apply eRS heRS X z)))
  refine eq_of_henselization_equiv (H.henselizationEquiv X) (H.henselizationMap X)
    (H.henselizationEquiv_algebraMap X) (RingEquiv.refl _)
    (J.map (algebraMap S (henselization S J : Type w))) (henselianPair_henselization S J)
    ((K'.functor.obj ((ringDeformationTransport eRS heRS).obj X)).hom.map.hom.comp
      (E X).toRingHom)
    (d.toRingHom.comp (H.functor.obj X).hom.map.hom) (fun z => ?_) (fun z hz => ?_) x
  · change (K'.functor.obj ((ringDeformationTransport eRS heRS).obj X)).hom.map.hom
        (E X (H.henselizationMap X z)) = d ((H.functor.obj X).hom.map.hom (H.henselizationMap X z))
    rw [hval, H.specialFiber_comm]
    exact (hchar _).symm
  · change (K'.functor.obj ((ringDeformationTransport eRS heRS).obj X)).hom.map.hom
      (E X (H.henselizationMap X z)) ∈ _
    rw [hval]
    exact Ideal.mem_map_of_mem _ (hmem _ (Ideal.mem_comap.mp hz))

include hE in
/-- **The fibre comparison of the congruence square is natural in morphisms of deformations.** -/
public theorem henselizationCongr_naturality
    (hmem : ∀ r : R, r ∈ I → eRS r ∈ J)
    {X Y : ringDeformationCategory (Λ := Λ) (k := k) R} (f : X ⟶ Y)
    (x : (H.functor.obj X).left.fiber) :
    E Y ((H.functor.map f).left.map.hom x) =
      (K'.functor.map ((ringDeformationTransport eRS heRS).map f)).left.map.hom (E X x) := by
  refine eq_of_henselization_equiv (H.henselizationEquiv X) (H.henselizationMap X)
    (H.henselizationEquiv_algebraMap X)
    (K'.henselizationEquiv ((ringDeformationTransport eRS heRS).obj Y)).symm
    ((J.comap ((ringDeformationTransport eRS heRS).obj Y).hom.map.hom).map
      (algebraMap ((ringDeformationTransport eRS heRS).obj Y).left.fiber
        (henselization ((ringDeformationTransport eRS heRS).obj Y).left.fiber
          (J.comap ((ringDeformationTransport eRS heRS).obj Y).hom.map.hom) : Type w)))
    (henselianPair_henselization _ _)
    ((E Y).toRingHom.comp (H.functor.map f).left.map.hom)
    ((K'.functor.map ((ringDeformationTransport eRS heRS).map f)).left.map.hom.comp
      (E X).toRingHom) (fun z => ?_) (fun z hz => ?_) x
  · change E Y ((H.functor.map f).left.map.hom (H.henselizationMap X z)) =
      (K'.functor.map ((ringDeformationTransport eRS heRS).map f)).left.map.hom
        (E X (H.henselizationMap X z))
    rw [← H.naturality, hE, hE]
    exact K'.naturality ((ringDeformationTransport eRS heRS).map f) z
  · change (K'.henselizationEquiv ((ringDeformationTransport eRS heRS).obj Y)).symm
      (E Y ((H.functor.map f).left.map.hom (H.henselizationMap X z))) ∈ _
    rw [← H.naturality, hE]
    refine Eq.mpr (congrArg (· ∈ _) (K'.henselizationEquiv_symm_henselizationMap
      ((ringDeformationTransport eRS heRS).obj Y) _))
      (Ideal.mem_map_of_mem _ (Ideal.mem_comap.mpr ?_))
    have h1 : ((ringDeformationTransport eRS heRS).obj Y).hom.map.hom (f.left.map.hom z) =
        eRS (X.hom.map.hom z) :=
      (ringDeformationTransport_specialFiber_apply eRS heRS Y (f.left.map.hom z)).trans
        (congrArg eRS (deformationMorphism_map_comm f z))
    exact Eq.mpr (congrArg (· ∈ J) h1) (hmem _ (Ideal.mem_comap.mp hz))

/-- **Henselization is compatible with transport along an isomorphism of the algebras being
henselized.** For an isomorphism `R ≅ S` of `k`-algebras carrying `I` to `J`, henselizing `R`
along `I` and transporting along the induced isomorphism `R^h_I ≅ S^h_J` is isomorphic, over
`𝒞_Λ`, to transporting along `R ≅ S` and then henselizing `S` along `J`.

The isomorphism `R^h_I ≅ S^h_J` and its compatibility with the maps out of `R` are hypotheses, not
existentials: they are what `Deformation.Examples.exists_ringEquiv_henselization_of_ringEquiv`
produces from the equality of ideals. -/
public theorem nonempty_basedIso_henselizationFunctor_congr
    (hIJ : I.map eRS.toRingHom = J)
    (hd : ∀ a : k, d (algebraMap k (henselization R I : Type w) a) =
      algebraMap k (henselization S J : Type w) a)
    (hchar : ∀ r : R, d (algebraMap R (henselization R I : Type w) r) =
      algebraMap S (henselization S J : Type w) (eRS r)) :
    Nonempty (BasedFunctor.comp (henselizationFunctor (Λ := Λ) (k := k) I).functor
        (ringDeformationTransport d hd) ≅
      BasedFunctor.comp (ringDeformationTransport eRS heRS)
        (henselizationFunctor (Λ := Λ) (k := k) J).functor) := by
  classical
  have hmem : ∀ r : R, r ∈ I → eRS r ∈ J := by
    intro r hr
    rw [← hIJ]
    exact Ideal.mem_map_of_mem _ hr
  have hmemiff : ∀ r : R, eRS r ∈ J → r ∈ I := by
    intro r hr
    rw [← hIJ] at hr
    have hr' : r ∈ (I.map eRS.toRingHom).comap eRS.toRingHom := hr
    rwa [Ideal.comap_map_of_bijective eRS.toRingHom eRS.bijective] at hr'
  have hI : ∀ X : ringDeformationCategory (Λ := Λ) (k := k) R,
      I.comap X.hom.map.hom =
        J.comap ((ringDeformationTransport eRS heRS).obj X).hom.map.hom := by
    intro X
    refine Ideal.ext fun z => ?_
    calc z ∈ I.comap X.hom.map.hom ↔ X.hom.map.hom z ∈ I := Ideal.mem_comap
      _ ↔ eRS (X.hom.map.hom z) ∈ J :=
          ⟨hmem _, hmemiff _⟩
      _ ↔ ((ringDeformationTransport eRS heRS).obj X).hom.map.hom z ∈ J :=
          iff_of_eq
            (congrArg (· ∈ J) (ringDeformationTransport_specialFiber_apply eRS heRS X z)).symm
      _ ↔ z ∈ J.comap ((ringDeformationTransport eRS heRS).obj X).hom.map.hom :=
          Ideal.mem_comap.symm
  let E : ∀ X : ringDeformationCategory (Λ := Λ) (k := k) R,
      ((henselizationFunctor (Λ := Λ) (k := k) I).functor.obj X).left.fiber ≃+*
        ((henselizationFunctor (Λ := Λ) (k := k) J).functor.obj
          ((ringDeformationTransport eRS heRS).obj X)).left.fiber := fun X =>
    (((henselizationFunctor (Λ := Λ) (k := k) I).henselizationEquiv X).symm).trans
      ((henselizationEquivOfIdealEq (I.comap X.hom.map.hom)
        (J.comap ((ringDeformationTransport eRS heRS).obj X).hom.map.hom) (hI X)).val.trans
        ((henselizationFunctor (Λ := Λ) (k := k) J).henselizationEquiv
          ((ringDeformationTransport eRS heRS).obj X)))
  have hE : ∀ (X : ringDeformationCategory (Λ := Λ) (k := k) R) (x : X.left.fiber),
      E X ((henselizationFunctor (Λ := Λ) (k := k) I).henselizationMap X x) =
        (henselizationFunctor (Λ := Λ) (k := k) J).henselizationMap
          ((ringDeformationTransport eRS heRS).obj X) x := by
    intro X x
    change (henselizationFunctor (Λ := Λ) (k := k) J).henselizationEquiv
      ((ringDeformationTransport eRS heRS).obj X)
      ((henselizationEquivOfIdealEq (I.comap X.hom.map.hom)
          (J.comap ((ringDeformationTransport eRS heRS).obj X).hom.map.hom) (hI X)).val
        (((henselizationFunctor (Λ := Λ) (k := k) I).henselizationEquiv X).symm
          ((henselizationFunctor (Λ := Λ) (k := k) I).henselizationMap X x))) = _
    have e1 := (henselizationFunctor (Λ := Λ) (k := k) I).henselizationEquiv_symm_henselizationMap
      X x
    refine Eq.trans (congrArg (fun u =>
      (henselizationFunctor (Λ := Λ) (k := k) J).henselizationEquiv
        ((ringDeformationTransport eRS heRS).obj X)
        ((henselizationEquivOfIdealEq (I.comap X.hom.map.hom)
          (J.comap ((ringDeformationTransport eRS heRS).obj X).hom.map.hom) (hI X)).val u))
      e1) ?_
    refine Eq.trans (congrArg
      ((henselizationFunctor (Λ := Λ) (k := k) J).henselizationEquiv
        ((ringDeformationTransport eRS heRS).obj X))
      ((henselizationEquivOfIdealEq (I.comap X.hom.map.hom)
        (J.comap ((ringDeformationTransport eRS heRS).obj X).hom.map.hom) (hI X)).property
        x)) ?_
    exact (henselizationFunctor (Λ := Λ) (k := k) J).henselizationEquiv_algebraMap
      ((ringDeformationTransport eRS heRS).obj X) x
  refine ⟨basedIsoOfFiberEquiv _ _ E (fun X a => ?_) (fun X x => ?_) (fun X Y f x => ?_)⟩
  · exact henselizationCongr_scalar_comm eRS heRS I J _ _ E hE X _ a
  · exact henselizationCongr_specialFiber_comm eRS heRS I J d _ _ E hE hmem hchar X x
  · exact henselizationCongr_naturality eRS heRS I J _ _ E hE hmem f x

end CongrComparison

/-! ### The comparison along the whole family of maximal ideals -/

section FamilyComparison

variable {P : Type w} [CommRing P] [Algebra k P] {ι : Type w} [Finite ι]
  (m : ι → PrimeSpectrum P)
  (H : HenselizationFunctorData (Λ := Λ) (k := k) (⨅ i, (m i).asIdeal))
  (L : ∀ i, LocalizationFunctorData (Λ := Λ) (k := k) (m i).asIdeal.primeCompl)
  (K' : ∀ i, HenselizationFunctorData (Λ := Λ) (k := k)
    (IsLocalRing.maximalIdeal (localRingAt (m i))))
  (E : ∀ X : ringDeformationCategory (Λ := Λ) (k := k) P,
    (H.functor.obj X).left.fiber ≃+*
      (∀ i, ((K' i).functor.obj ((L i).functor.obj X)).left.fiber))
  (hE : ∀ (X : ringDeformationCategory (Λ := Λ) (k := k) P) (x : X.left.fiber) (i : ι),
    E X (H.henselizationMap X x) i =
      (K' i).henselizationMap ((L i).functor.obj X) ((L i).localizationMap X x))

omit [Finite ι] in
/-- The decomposition `P^h_J ≅ ∏ P^h_{𝔪 i}` is `k`-linear: both sides are `k`-algebras through
`P`, and the isomorphism is compatible with the maps out of `P`. -/
public theorem algebraMap_comm_of_henselizationPiRingEquiv
    (e : (henselization P (⨅ i, (m i).asIdeal) : Type w) ≃+*
      (∀ i, henselizedLocalRingAt (m i)))
    (hchar : ∀ (r : P) (i : ι),
      e (algebraMap P (henselization P (⨅ j, (m j).asIdeal) : Type w) r) i =
        algebraMap (localRingAt (m i)) (henselizedLocalRingAt (m i))
          (algebraMap P (localRingAt (m i)) r)) :
    ∀ a : k, e (algebraMap k (henselization P (⨅ i, (m i).asIdeal) : Type w) a) =
      algebraMap k (∀ i, henselizedLocalRingAt (m i)) a := by
  intro a
  funext i
  let : IsScalarTower k P (henselization P (⨅ j, (m j).asIdeal) : Type w) :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  let : IsScalarTower k (localRingAt (m i)) (henselizedLocalRingAt (m i)) :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  rw [IsScalarTower.algebraMap_apply k P (henselization P (⨅ j, (m j).asIdeal) : Type w),
    hchar, Pi.algebraMap_apply,
    IsScalarTower.algebraMap_apply k (localRingAt (m i)) (henselizedLocalRingAt (m i)),
    IsScalarTower.algebraMap_apply k P (localRingAt (m i))]

omit [Finite ι] in
include hE in
/-- **The fibre comparison of the family is linear over the Artinian base, componentwise.** -/
public theorem henselizedLocalizationFamily_scalar_comm
    (X : ringDeformationCategory (Λ := Λ) (k := k) P) (i : ι)
    (hp : (H.functor.obj X).left.base = X.left.base)
    (hq : ((K' i).functor.obj ((L i).functor.obj X)).left.base = X.left.base)
    (a : (H.functor.obj X).left.base) :
    E X (algebraMap (H.functor.obj X).left.base (H.functor.obj X).left.fiber a) i =
      algebraMap ((K' i).functor.obj ((L i).functor.obj X)).left.base
        ((K' i).functor.obj ((L i).functor.obj X)).left.fiber
        ((eqToHom hq.symm).hom ((eqToHom hp).hom a)) := by
  refine Eq.trans (congrArg (fun z => E X z i) (H.algebraMap_base X a)) ?_
  refine Eq.trans (hE X _ i) ?_
  refine Eq.trans ?_ ((K' i).algebraMap_base ((L i).functor.obj X) _).symm
  refine congrArg ((K' i).henselizationMap ((L i).functor.obj X)) ?_
  refine Eq.trans ?_ ((L i).algebraMap_base X _).symm
  refine congrArg (fun z => (L i).localizationMap X
    (algebraMap X.left.base X.left.fiber z)) ?_
  exact ((eqToHom_hom_trans₂ hq.symm ((K' i).functor.w_obj ((L i).functor.obj X))
    ((L i).functor.w_obj X) rfl ((eqToHom hp).hom a)).trans
    (eqToHom_hom_refl rfl ((eqToHom hp).hom a))).symm

omit [Finite ι] in
include hE in
/-- **The fibre comparison of the family commutes with the reduction to the special fibre,
componentwise.** -/
public theorem henselizedLocalizationFamily_specialFiber_comm
    (e : (henselization P (⨅ i, (m i).asIdeal) : Type w) ≃+*
      (∀ i, henselizedLocalRingAt (m i)))
    (hchar : ∀ (r : P) (i : ι),
      e (algebraMap P (henselization P (⨅ j, (m j).asIdeal) : Type w) r) i =
        algebraMap (localRingAt (m i)) (henselizedLocalRingAt (m i))
          (algebraMap P (localRingAt (m i)) r))
    (X : ringDeformationCategory (Λ := Λ) (k := k) P) (i : ι)
    (x : (H.functor.obj X).left.fiber) :
    ((K' i).functor.obj ((L i).functor.obj X)).hom.map.hom (E X x i) =
      e ((H.functor.obj X).hom.map.hom x) i := by
  have hval : ∀ z : X.left.fiber,
      ((K' i).functor.obj ((L i).functor.obj X)).hom.map.hom (E X (H.henselizationMap X z) i) =
        algebraMap (localRingAt (m i)) (henselizedLocalRingAt (m i))
          (algebraMap P (localRingAt (m i)) (X.hom.map.hom z)) := fun z =>
    (congrArg _ (hE X z i)).trans
      (((K' i).specialFiber_comm ((L i).functor.obj X) _).trans
        (congrArg (algebraMap (localRingAt (m i)) (henselizedLocalRingAt (m i)))
          ((L i).specialFiber_comm X z).symm))
  refine eq_of_henselization_equiv (H.henselizationEquiv X) (H.henselizationMap X)
    (H.henselizationEquiv_algebraMap X) (RingEquiv.refl _) (henselizedMaximalIdealAt (m i))
    (henselianPair_henselization (localRingAt (m i))
      (IsLocalRing.maximalIdeal (localRingAt (m i))))
    (((K' i).functor.obj ((L i).functor.obj X)).hom.map.hom.comp
      ((Pi.evalRingHom
        (fun j => ((K' j).functor.obj ((L j).functor.obj X)).left.fiber) i).comp
        (E X).toRingHom))
    ((Pi.evalRingHom (fun j => henselizedLocalRingAt (m j)) i).comp
      (e.toRingHom.comp (H.functor.obj X).hom.map.hom)) (fun z => ?_) (fun z hz => ?_) x
  · change ((K' i).functor.obj ((L i).functor.obj X)).hom.map.hom
        (E X (H.henselizationMap X z) i) =
      e ((H.functor.obj X).hom.map.hom (H.henselizationMap X z)) i
    rw [hval, H.specialFiber_comm]
    exact (hchar _ i).symm
  · change ((K' i).functor.obj ((L i).functor.obj X)).hom.map.hom
      (E X (H.henselizationMap X z) i) ∈ _
    rw [hval]
    exact Ideal.mem_map_of_mem _ ((IsLocalization.AtPrime.map_eq_maximalIdeal (m i).asIdeal
      (localRingAt (m i))).le (Ideal.mem_map_of_mem _
        (iInf_le (fun j => (m j).asIdeal) i (Ideal.mem_comap.mp hz))))

omit [Finite ι] in
include hE in
/-- **The fibre comparison of the family is natural in morphisms of deformations,
componentwise.** -/
public theorem henselizedLocalizationFamily_naturality
    {X Y : ringDeformationCategory (Λ := Λ) (k := k) P} (f : X ⟶ Y) (i : ι)
    (x : (H.functor.obj X).left.fiber) :
    E Y ((H.functor.map f).left.map.hom x) i =
      ((K' i).functor.map ((L i).functor.map f)).left.map.hom (E X x i) := by
  refine eq_of_henselization_equiv (H.henselizationEquiv X) (H.henselizationMap X)
    (H.henselizationEquiv_algebraMap X) ((K' i).henselizationEquiv ((L i).functor.obj Y)).symm
    (((IsLocalRing.maximalIdeal (localRingAt (m i))).comap
      ((L i).functor.obj Y).hom.map.hom).map (algebraMap ((L i).functor.obj Y).left.fiber
        (henselization ((L i).functor.obj Y).left.fiber
          ((IsLocalRing.maximalIdeal (localRingAt (m i))).comap
            ((L i).functor.obj Y).hom.map.hom) : Type w)))
    (henselianPair_henselization _ _)
    ((Pi.evalRingHom (fun j => ((K' j).functor.obj ((L j).functor.obj Y)).left.fiber) i).comp
      ((E Y).toRingHom.comp (H.functor.map f).left.map.hom))
    (((K' i).functor.map ((L i).functor.map f)).left.map.hom.comp
      ((Pi.evalRingHom (fun j => ((K' j).functor.obj ((L j).functor.obj X)).left.fiber) i).comp
        (E X).toRingHom)) (fun z => ?_) (fun z hz => ?_) x
  · change E Y ((H.functor.map f).left.map.hom (H.henselizationMap X z)) i =
      ((K' i).functor.map ((L i).functor.map f)).left.map.hom
        (E X (H.henselizationMap X z) i)
    rw [← H.naturality, hE, hE]
    exact (congrArg _ ((L i).naturality f z)).trans
      ((K' i).naturality ((L i).functor.map f) _)
  · change ((K' i).henselizationEquiv ((L i).functor.obj Y)).symm
      (E Y ((H.functor.map f).left.map.hom (H.henselizationMap X z)) i) ∈ _
    refine Eq.mpr (congrArg (· ∈ _) (((congrArg _ ((congrArg (fun u => E Y u i)
      (H.naturality f z).symm).trans (hE Y _ i))).trans
      ((K' i).henselizationEquiv_symm_henselizationMap ((L i).functor.obj Y) _))))
      (Ideal.mem_map_of_mem _ (Ideal.mem_comap.mpr ?_))
    have h1 : ((L i).functor.obj Y).hom.map.hom ((L i).localizationMap Y (f.left.map.hom z)) =
        algebraMap P (localRingAt (m i)) (X.hom.map.hom z) :=
      ((L i).specialFiber_comm Y (f.left.map.hom z)).symm.trans
        (congrArg (algebraMap P (localRingAt (m i))) (deformationMorphism_map_comm f z))
    exact Eq.mpr (congrArg (· ∈ IsLocalRing.maximalIdeal (localRingAt (m i))) h1)
      ((IsLocalization.AtPrime.map_eq_maximalIdeal (m i).asIdeal (localRingAt (m i))).le
        (Ideal.mem_map_of_mem _ (iInf_le (fun j => (m j).asIdeal) i (Ideal.mem_comap.mp hz))))

/-- **Stacks 0DZF, the comparison the source's proof makes.** Henselizing a deformation of `P`
along `J = 𝔪 1 ∩ … ∩ 𝔪 n` and then transporting along the decomposition
`P^h_J ≅ ∏ P^h_{𝔪 i}` is isomorphic, over `𝒞_Λ`, to localizing at each `𝔪 i`, henselizing each
of the resulting local rings, and reading the family of deformations so obtained as a deformation
of the product ring.

This is what makes precise the step the source takes when, having applied **Stacks 0DZD** to `P`
itself with the ideal `J` — where the finite type hypothesis genuinely holds — it says
"`P^h = ∏ P^h_{𝔪 i}`" and reads the conclusion at the product.

The decomposition isomorphism and its compatibility with the maps out of `P` are hypotheses, not
existentials: they are exactly what
`Deformation.Examples.exists_ringEquiv_henselization_iInf_pi_henselizedLocalRing` produces. -/
public theorem nonempty_basedIso_henselizationPi
    (hmax : ∀ i, (m i).asIdeal.IsMaximal) (hinj : Function.Injective m)
    (e : (henselization P (⨅ i, (m i).asIdeal) : Type w) ≃+*
      (∀ i, henselizedLocalRingAt (m i)))
    (he : ∀ a : k,
      e (algebraMap k (henselization P (⨅ i, (m i).asIdeal) : Type w) a) =
        algebraMap k (∀ i, henselizedLocalRingAt (m i)) a)
    (hchar : ∀ (r : P) (i : ι),
      e (algebraMap P (henselization P (⨅ j, (m j).asIdeal) : Type w) r) i =
        algebraMap (localRingAt (m i)) (henselizedLocalRingAt (m i))
          (algebraMap P (localRingAt (m i)) r)) :
    Nonempty (BasedFunctor.comp
        (henselizationFunctor (Λ := Λ) (k := k) (⨅ i, (m i).asIdeal)).functor
        (ringDeformationTransport e he) ≅
      BasedFunctor.comp (localizationFunctors (Λ := Λ) (k := k) m)
        (BasedFunctor.comp (henselizationFunctors (Λ := Λ) (k := k) m)
          (piDeformationFunctor (fun i => henselizedLocalRingAt (m i))))) := by
  classical
  let Hd := henselizationFunctor (Λ := Λ) (k := k) (⨅ j, (m j).asIdeal)
  let Ld := fun i => localizationFunctor (Λ := Λ) (k := k) (m i).asIdeal.primeCompl
  let Kd := fun i => henselizationFunctor (Λ := Λ) (k := k)
    (IsLocalRing.maximalIdeal (localRingAt (m i)))
  choose E hE using fun X => exists_ringEquiv_henselizedLocalizationFamilyFiber
    (Λ := Λ) (k := k) m hmax hinj X
  have hzi : ∀ (X : ringDeformationCategory (Λ := Λ) (k := k) P) (i : ι),
      ((Kd i).functor.obj ((Ld i).functor.obj X)).left.base = X.left.base := fun X i =>
    ((Kd i).functor.w_obj ((Ld i).functor.obj X)).trans ((Ld i).functor.w_obj X)
  refine ⟨basedIsoOfFiberEquiv _ _ E (fun X a => ?_) (fun X x => ?_) (fun X Y f x => ?_)⟩
  · funext i
    refine Eq.trans ?_ (flatAlgebraWithBase_algebraMap X.left.base
      ((Kd i).functor.obj ((Ld i).functor.obj X)).left (hzi X i) _).symm
    exact henselizedLocalizationFamily_scalar_comm m Hd Ld Kd E hE X i
      (Hd.functor.w_obj X) (hzi X i) a
  · funext i
    exact henselizedLocalizationFamily_specialFiber_comm m Hd Ld Kd E hE e hchar X i x
  · funext i
    exact henselizedLocalizationFamily_naturality m Hd Ld Kd E hE f i x

end FamilyComparison

end Deformation.Examples
