module

public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.RingTheory.Noetherian.Nilpotent
public import StacksFrontier.AlgebraicGeometry.FormalSpace.CompletionMorphismsAffine
public import StacksFrontier.AlgebraicGeometry.FormalSpace.MorphismUniquenessAlongClosedSubset
public import StacksFrontier.AlgebraicGeometry.FormalSpace.SchemeAtlas
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsRepresentable

/-!
# Morphisms out of the completion of a locally Noetherian scheme

Let `V` be a locally Noetherian scheme in the big fppf site over `S` and let `Z ⊆ |V|` be a
closed subset. A morphism of schemes `x : U ⟶ V` whose image lies in `Z` factors, locally on
`U`, through a Noetherian closed subscheme of an affine open of `V` with underlying set in `Z`.
Consequently a morphism out of the completion `V_{/Z}` of Stacks 0AIX into an fppf sheaf is
determined by its values on the sections `N ⟶ V` with image in `Z` and `N` locally Noetherian.

## Main results

* `AlgebraicGeometry.Scheme.exists_factor_isLocallyNoetherian_of_range_subset`: the local
  factorization through a Noetherian closed subscheme of an affine open.
* `AlgebraicGeometry.FormalSpace.completionSheaf_yoneda_hom_ext_of_isLocallyNoetherian`: the
  extensionality principle for morphisms out of `V_{/Z}`.

## References

* [Stacks Project, Tag 0AIX](https://stacks.math.columbia.edu/tag/0AIX)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry

/-- A morphism `x : U ⟶ V` into a locally Noetherian scheme whose image lies in a closed subset
`Ws` factors, near any point of `U`, through a monomorphism `N ⟶ V` from a locally Noetherian
scheme whose image lies in `Ws`. -/
theorem Scheme.exists_factor_isLocallyNoetherian_of_range_subset {U V : Scheme.{u}}
    [IsLocallyNoetherian V] (x : U ⟶ V) {Ws : Set V} (hWs : IsClosed Ws)
    (hx : Set.range x.base ⊆ Ws) (u : U) :
    ∃ (O : U.Opens) (N : Scheme.{u}) (n : N ⟶ V) (y : O.toScheme ⟶ N),
      u ∈ O ∧ Mono n ∧ IsLocallyNoetherian N ∧ Set.range n.base ⊆ Ws ∧ y ≫ n = O.ι ≫ x := by
  obtain ⟨A, hA', hxA, -⟩ := exists_isAffineOpen_mem_and_subset (U := ⊤) (x := x.base u)
    (by simp)
  obtain ⟨O, hO', huO, hOA₀⟩ := exists_isAffineOpen_mem_and_subset (U := x ⁻¹ᵁ A) (x := u) hxA
  have hOA : O ≤ x ⁻¹ᵁ A := hOA₀
  have : IsNoetherianRing Γ(V, A) := IsLocallyNoetherian.component_noetherian ⟨A, hA'⟩
  let W' : Set (PrimeSpectrum Γ(V, A)) := hA'.fromSpec.base ⁻¹' Ws
  have hW' : IsClosed W' := hWs.preimage hA'.fromSpec.base.hom.continuous
  let I : Ideal Γ(V, A) := PrimeSpectrum.vanishingIdeal W'
  have hIfg : I.FG := IsNoetherian.noetherian I
  let φ := x.appLE A O hOA
  have hnil : I.map φ.hom ≤ _root_.nilradical (U.presheaf.obj (op O)) := by
    rw [Ideal.map_le_iff_le_comap]
    intro f hf
    show IsNilpotent (φ f)
    have hempty : U.basicOpen (φ f) = ⊥ := by
      show U.basicOpen (x.appLE A O hOA f) = ⊥
      rw [Scheme.basicOpen_appLE]
      ext o
      simp only [TopologicalSpace.Opens.coe_inf, Set.mem_inter_iff, SetLike.mem_coe,
        TopologicalSpace.Opens.mem_bot, iff_false, not_and]
      intro _ ho
      have hmem : x.base o ∈ V.basicOpen f := ho
      obtain ⟨p, hp⟩ : x.base o ∈ Set.range hA'.fromSpec.base := by
        rw [hA'.range_fromSpec]; exact V.basicOpen_le f hmem
      have hpW : p ∈ W' := by
        show hA'.fromSpec.base p ∈ Ws
        rw [hp]; exact hx ⟨o, rfl⟩
      have hpb : p ∈ hA'.fromSpec ⁻¹ᵁ V.basicOpen f := by
        show hA'.fromSpec.base p ∈ V.basicOpen f
        rw [hp]; exact hmem
      rw [hA'.fromSpec_preimage_basicOpen] at hpb
      exact hpb ((PrimeSpectrum.mem_vanishingIdeal W' f).mp hf p hpW)
    have h := hO'.fromSpec_preimage_basicOpen (φ f)
    rw [hempty] at h
    refine (PrimeSpectrum.basicOpen_eq_bot_iff _).mp ?_
    rw [← h]
    ext z
    simp only [Hom.preimage_bot, TopologicalSpace.Opens.coe_bot, Set.mem_empty_iff_false, false_iff]
    exact fun hz => (hz : False)
  obtain ⟨m, hm⟩ := Ideal.exists_pow_le_of_le_radical_of_fg hnil (hIfg.map _)
  have hker : I ^ m ≤ RingHom.ker φ.hom := fun a ha =>
    Ideal.mem_bot.mp (hm (Ideal.map_pow φ.hom I m ▸ Ideal.mem_map_of_mem _ ha :
      φ.hom a ∈ (I.map φ.hom) ^ m))
  let lift : Γ(V, A) ⧸ I ^ m →+* U.presheaf.obj (op O) := Ideal.Quotient.lift (I ^ m) φ.hom hker
  let n : Spec (CommRingCat.of (Γ(V, A) ⧸ I ^ m)) ⟶ V :=
    Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ m))) ≫ hA'.fromSpec
  have : IsClosedImmersion (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ m)))) :=
    IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
  refine ⟨O, _, n, hO'.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom lift), huO, inferInstance,
    inferInstance, ?_, ?_⟩
  · rintro _ ⟨q, rfl⟩
    show PrimeSpectrum.comap (Ideal.Quotient.mk (I ^ m)) q ∈ W'
    rw [← hW'.closure_eq, ← PrimeSpectrum.zeroLocus_vanishingIdeal_eq_closure]
    intro f hf
    exact (PrimeSpectrum.comap (Ideal.Quotient.mk (I ^ m)) q).isPrime.mem_of_pow_mem m
      (show Ideal.Quotient.mk (I ^ m) (f ^ m) ∈ q.asIdeal by
        rw [Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.pow_mem_pow hf m)]
        exact q.asIdeal.zero_mem)
  · have hcomp : CommRingCat.ofHom (Ideal.Quotient.mk (I ^ m)) ≫ CommRingCat.ofHom lift = φ := by
      ext a; rfl
    simp only [n, Category.assoc, ← Spec.map_comp_assoc, hcomp]
    rw [IsAffineOpen.SpecMap_appLE_fromSpec x hA' hO' hOA, ← IsAffineOpen.isoSpec_inv_ι,
      Category.assoc, Iso.hom_inv_id_assoc]

namespace FormalSpace

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

attribute [local instance] Space.pointTopology

/-- A morphism `x : N ⟶ V` of the site has point-set image in a set `Z` of points of `V`
exactly when the underlying morphism of schemes has image in the corresponding set of points
of the scheme `V`. -/
theorem hasImageIn_yoneda_iff_range_subset {N V : BigFppfOver B S hS}
    (Z : Set (Space.points B S hS (yoneda.obj V))) (x : N ⟶ V) :
    Space.HasImageIn B S hS (yoneda.obj V) Z N x ↔
      Set.range ((BigFppfOver.toScheme B S hS).map x).base ⊆
        Space.pointsToScheme B S hS V '' Z := by
  have hy : yonedaEquiv.symm x = yoneda.map x := by
    rw [Equiv.symm_apply_eq, yonedaEquiv_yoneda_map]
  rw [Space.hasImageIn_iff_range_subset, hy]
  constructor
  · rintro h _ ⟨p, rfl⟩
    obtain ⟨w, rfl⟩ := Space.surjective_pointsToScheme B S hS N p
    rw [← Space.pointsToScheme_pointsMap_yoneda]
    exact ⟨_, h ⟨w, rfl⟩, rfl⟩
  · rintro h _ ⟨w, rfl⟩
    have hw := h ⟨Space.pointsToScheme B S hS N w, rfl⟩
    rw [← Space.pointsToScheme_pointsMap_yoneda] at hw
    obtain ⟨z, hz, hzeq⟩ := hw
    rwa [← Space.injective_pointsToScheme B S hS V hzeq]

/-- **Morphisms out of the completion of a locally Noetherian scheme are determined on
Noetherian thickenings.** Let `V` be a locally Noetherian object of the big fppf site over `S`
and `Z ⊆ |V|` closed. Two morphisms `V_{/Z} ⟶ G` into an fppf sheaf agree as soon as they
agree on the sections of `V_{/Z}` given by the morphisms `N ⟶ V` with point-set image in `Z`
and `N` locally Noetherian. -/
theorem completionSheaf_yoneda_hom_ext_of_isLocallyNoetherian {V : BigFppfOver B S hS}
    [IsLocallyNoetherian ((BigFppfOver.toScheme B S hS).obj V)]
    {Z : Set (Space.points B S hS (yoneda.obj V))} (hZ : IsClosed Z)
    {G : Sheaf (BigFppfOver.topology B S hS) (Type (u + 1))}
    {φ ψ : Space.completionSheaf B S hS (yoneda.obj V) Z ⟶ G}
    (H : ∀ (N : BigFppfOver B S hS), IsLocallyNoetherian ((BigFppfOver.toScheme B S hS).obj N) →
      ∀ (x : N ⟶ V) (hx : Space.HasImageIn B S hS (yoneda.obj V) Z N x),
        φ.hom.app (op N) (presheafSection B S hS x hx) =
          ψ.hom.app (op N) (presheafSection B S hS x hx)) :
    φ = ψ := by
  have hWs : IsClosed (Space.pointsToScheme B S hS V '' Z) :=
    (Space.isClosed_pointTopology_yoneda_iff_isClosed_image B S hS V Z).mp hZ
  apply Sheaf.hom_ext
  apply (BigFppfOver.topology B S hS).sheafify_hom_ext _ _ G.property
  ext W ⟨⟨x⟩, hx⟩
  show φ.hom.app W (presheafSection B S hS x hx) = ψ.hom.app W (presheafSection B S hS x hx)
  have hrange := (hasImageIn_yoneda_iff_range_subset B S hS Z x).mp hx
  choose O N n y huO hmono hN hn hyn using fun w : (BigFppfOver.toScheme B S hS).obj W.unop =>
    Scheme.exists_factor_isLocallyNoetherian_of_range_subset
      ((BigFppfOver.toScheme B S hS).map x) hWs hrange w
  let Ow : (BigFppfOver.toScheme B S hS).obj W.unop → BigFppfOver B S hS := fun w =>
    BigFppfOver.mk B S hS (B.contains_of_mono (O w).ι W.unop.left.2)
      ((O w).ι ≫ B.inclusion.map W.unop.hom)
  let k : ∀ w, Ow w ⟶ W.unop := fun w =>
    Over.homMk (ObjectProperty.homMk (O w).ι) (by apply ObjectProperty.hom_ext; rfl)
  let Nw : (BigFppfOver.toScheme B S hS).obj W.unop → BigFppfOver B S hS := fun w =>
    have := hmono w
    BigFppfOver.mk B S hS (B.contains_of_mono (n w) V.left.2) (n w ≫ B.inclusion.map V.hom)
  let nw : ∀ w, Nw w ⟶ V := fun w =>
    Over.homMk (ObjectProperty.homMk (n w)) (by apply ObjectProperty.hom_ext; rfl)
  have hxw : ∀ w, (O w).ι ≫ (BigFppfOver.toScheme B S hS).map x ≫ B.inclusion.map V.hom =
      (O w).ι ≫ B.inclusion.map W.unop.hom := fun w => by
    show (O w).ι ≫ B.inclusion.map x.left ≫ B.inclusion.map V.hom = _
    rw [← B.inclusion.map_comp]
    exact congrArg (fun t => (O w).ι ≫ B.inclusion.map t) (Over.w x)
  let yw : ∀ w, Ow w ⟶ Nw w := fun w =>
    Over.homMk (ObjectProperty.homMk (y w)) (by
      apply ObjectProperty.hom_ext
      show y w ≫ n w ≫ B.inclusion.map V.hom = (O w).ι ≫ B.inclusion.map W.unop.hom
      rw [← Category.assoc, hyn w, Category.assoc, hxw w])
  have hfac : ∀ w, k w ≫ x = yw w ≫ nw w := fun w =>
    Over.OverMorphism.ext (B.inclusion.map_injective (hyn w).symm)
  have hmem := FormalSpace.fppf_ofArrows_mem B S hS Ow k
    (fun w => by change Flat (O w).ι; infer_instance)
    (fun w => by change LocallyOfFinitePresentation (O w).ι; infer_instance)
    (fun w => ⟨w, by change w ∈ Set.range (O w).ι; rw [Scheme.Opens.range_ι]; exact huO w⟩)
  refine ConcreteCategory.congr_hom (G.property.hom_ext_ofArrows k hmem
    (x := (↾fun _ : PUnit.{u + 2} => φ.hom.app W (presheafSection B S hS x hx)))
    (y := (↾fun _ : PUnit.{u + 2} => ψ.hom.app W (presheafSection B S hS x hx))) ?_) PUnit.unit
  intro w
  ext _
  show G.obj.map (k w).op (φ.hom.app W (presheafSection B S hS x hx)) =
    G.obj.map (k w).op (ψ.hom.app W (presheafSection B S hS x hx))
  have hmap : ∀ {M} (f : Ow w ⟶ M) a,
      Space.HasImageIn B S hS (yoneda.obj V) Z M a →
        Space.HasImageIn B S hS (yoneda.obj V) Z (Ow w) ((yoneda.obj V).map f.op a) :=
    fun f _ ha => (Space.completionSubfunctor B S hS (yoneda.obj V) Z).map f.op ha
  have hnw : Space.HasImageIn B S hS (yoneda.obj V) Z (Nw w) (nw w) :=
    (hasImageIn_yoneda_iff_range_subset B S hS Z (nw w)).mpr (hn w)
  have hx' := hmap (k w) x hx
  have hy' := hmap (yw w) _ hnw
  have heq : (yoneda.obj V).map (k w).op x = (yoneda.obj V).map (yw w).op (nw w) := hfac w
  have key : ∀ χ : Space.completionSheaf B S hS (yoneda.obj V) Z ⟶ G,
      G.obj.map (k w).op (χ.hom.app W (presheafSection B S hS x hx)) =
        G.obj.map (yw w).op (χ.hom.app (op (Nw w)) (presheafSection B S hS (nw w) hnw)) := by
    intro χ
    rw [← NatTrans.naturality_apply χ.hom, ← NatTrans.naturality_apply χ.hom,
      presheafSection_map B S hS (k w) x hx hx', presheafSection_map B S hS (yw w) _ hnw hy']
    have pc : ∀ (a b : (yoneda.obj V).obj (op (Ow w))) (_ : a = b)
        (ha : Space.HasImageIn B S hS (yoneda.obj V) Z (Ow w) a)
        (hb : Space.HasImageIn B S hS (yoneda.obj V) Z (Ow w) b),
        presheafSection B S hS a ha = presheafSection B S hS b hb := fun _ _ h _ _ => by
      subst h; rfl
    rw [pc _ _ heq hx' hy']
  rw [key φ, key ψ, H (Nw w) (hN w) (nw w) hnw]

end FormalSpace

end AlgebraicGeometry

end
