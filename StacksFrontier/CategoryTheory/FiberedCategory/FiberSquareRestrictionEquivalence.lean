module

public import StacksFrontier.AlgebraicGeometry.Quot.PolarizedPushout

/-!
# When the comparison functor of a square of fibre categories is an equivalence

Let `p : 𝒳 ⥤ 𝒮` be a fibred category and let

```
U  --i-->  U'
|          |
q          r
|          |
v          v
V  --w-->  V'
```

be a commutative square in `𝒮`. The comparison functor
`CategoryTheory.Functor.fiberSquareRestriction` takes an object of the fibre over `V'` to its two
base changes to `V` and to `U'` together with the canonical identification of their base changes
to `U`; it lands in the 2-fibre product `p_V ×_{p_U} p_{U'}` of fibre categories. This file
gives two criteria, phrased with arbitrary cartesian morphisms of `𝒳` rather than with the chosen
base changes, for that functor to be fully faithful and essentially surjective.

* **Gluing of morphisms.** If for every `a` over `V'` there is a commutative square of morphisms
  of `𝒳` lying over the square of the base, with cartesian sides `a_V ⟶ a` over `w` and
  `a_{U'} ⟶ a` over `r`, such that morphisms out of `a_V` over `w` and out of `a_{U'}` over `r`
  which agree on `a_U` glue to a unique morphism out of `a` over the identity, then the comparison
  functor is fully faithful.
* **Gluing of objects.** If every span `x_V ⟵ x_U ⟶ x_{U'}` of cartesian morphisms over
  `V ⟵ U ⟶ U'`, with `x_V` and `x_{U'}` in the fibres, is the restriction of an object `a` over
  `V'` along cartesian morphisms `x_V ⟶ a` and `x_{U'} ⟶ a` making the square commute, then the
  comparison functor is essentially surjective.

Being phrased with arbitrary cartesian morphisms, the criteria can be checked on whatever
presentation of the base changes is most convenient: the chosen cartesian lifts of the fibred
structure enter only in the proofs here.

## Main results

* `CategoryTheory.Functor.fiberInclusion_map_fiberPullbackSquareIso_hom_app`: the canonical
  identification of the two iterated base changes is compatible with the cartesian morphisms.
* `CategoryTheory.Functor.fiberSquareRestriction_faithful` and
  `CategoryTheory.Functor.fiberSquareRestriction_full`: the first criterion.
* `CategoryTheory.Functor.fiberSquareRestriction_essSurj`: the second criterion.
* `CategoryTheory.Functor.isEquivalence_fiberSquareRestriction`: both together.

## References

* [Stacks Project, Tag 0D44](https://stacks.math.columbia.edu/tag/0D44)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Limits.CategoricalPullback

universe v₁ u₁ v₂ u₂

namespace CategoryTheory.Functor

variable {𝒮 : Type u₁} {𝒳 : Type u₂} [Category.{v₁} 𝒮] [Category.{v₂} 𝒳] (p : 𝒳 ⥤ 𝒮)
  [p.IsFibered]

/-- The transport between the base changes along two equal morphisms is compatible with the
cartesian morphisms. -/
@[reassoc]
theorem fiberInclusion_map_eqToHom_app_comp_fiberPullbackHom {R S : 𝒮} {k k' : R ⟶ S}
    (h : k = k') (a : p.Fiber S) :
    Fiber.fiberInclusion.map
        ((eqToHom (congrArg (fun k : R ⟶ S ↦ fiberPullback p k) h)).app a) ≫
      fiberPullbackHom p k' a = fiberPullbackHom p k a := by
  subst h
  simp

section Square

variable {U U' V V' : 𝒮} (i : U ⟶ U') (q : U ⟶ V) (r : U' ⟶ V') (w : V ⟶ V')
  (hsq : q ≫ w = i ≫ r)

/-- **The identification of the two iterated base changes is compatible with the cartesian
morphisms**: followed by the cartesian morphisms down to `a`, it carries the composite through
`V` to the composite through `U'`. -/
@[reassoc]
theorem fiberInclusion_map_fiberPullbackSquareIso_hom_app (a : p.Fiber V') :
    Fiber.fiberInclusion.map ((fiberPullbackSquareIso p i q r w hsq).hom.app a) ≫
        fiberPullbackHom p i ((fiberPullback p r).obj a) ≫ fiberPullbackHom p r a =
      fiberPullbackHom p q ((fiberPullback p w).obj a) ≫ fiberPullbackHom p w a := by
  have h3 : Fiber.fiberInclusion.map ((fiberPullbackCompIso p i r).inv.app a) ≫
      fiberPullbackHom p i ((fiberPullback p r).obj a) ≫ fiberPullbackHom p r a =
        fiberPullbackHom p (i ≫ r) a := by
    rw [← fiberInclusion_map_fiberPullbackCompIsoApp_hom p i r a, ← Functor.map_comp_assoc]
    change Fiber.fiberInclusion.map ((fiberPullbackCompIsoApp p i r a).inv ≫
      (fiberPullbackCompIsoApp p i r a).hom) ≫ _ = _
    rw [Iso.inv_hom_id, Functor.map_id, Category.id_comp]
  simp only [fiberPullbackSquareIso, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Functor.map_comp, Category.assoc, eqToIso.hom]
  rw [h3, fiberInclusion_map_eqToHom_app_comp_fiberPullbackHom p hsq]
  exact fiberInclusion_map_fiberPullbackCompIsoApp_hom p q w a

/-- The structure isomorphism of the comparison functor at `a` is the identification of the two
iterated base changes of `a`. -/
@[simp]
theorem fiberSquareRestriction_obj_iso (a : p.Fiber V') :
    ((fiberSquareRestriction p i q r w hsq).obj a).iso =
      (fiberPullbackSquareIso p i q r w hsq).app a :=
  rfl

/-- A morphism of fibres has the given base change iff the corresponding square with a cartesian
morphism `c`, identified with the chosen one, commutes. -/
private theorem fiberPullback_map_eq_iff {R S : 𝒮} (k : R ⟶ S) {a b : p.Fiber S} {x : 𝒳}
    (c : x ⟶ Fiber.fiberInclusion.obj a) [p.IsCartesian k c] (φ : a ⟶ b)
    (σ : (fiberPullback p k).obj a ⟶ (fiberPullback p k).obj b) :
    (fiberPullback p k).map φ = σ ↔
      c ≫ Fiber.fiberInclusion.map φ =
        (IsCartesian.domainUniqueUpToIso p k (fiberPullbackHom p k a) c).hom ≫
          Fiber.fiberInclusion.map σ ≫ fiberPullbackHom p k b := by
  have h : (IsCartesian.domainUniqueUpToIso p k (fiberPullbackHom p k a) c).hom ≫
      fiberPullbackHom p k a = c := IsCartesian.fac p k _ c
  generalize IsCartesian.domainUniqueUpToIso p k (fiberPullbackHom p k a) c = e at h ⊢
  rw [← h, Category.assoc, cancel_epi, ← fiberPullback_map_fac]
  exact ⟨fun h ↦ by rw [h], fun h ↦ Fiber.hom_ext (IsCartesian.ext p k _ _ _ h)⟩

/-- **Gluing of morphisms along a square makes the comparison functor faithful.** -/
theorem fiberSquareRestriction_faithful
    (hFF : ∀ a : p.Fiber V', ∃ (aV aU' aU : 𝒳) (c : aV ⟶ Fiber.fiberInclusion.obj a)
      (d : aU' ⟶ Fiber.fiberInclusion.obj a) (u : aU ⟶ aV) (v : aU ⟶ aU'),
      p.IsCartesian w c ∧ p.IsCartesian r d ∧ p.IsHomLift q u ∧ p.IsHomLift i v ∧
        u ≫ c = v ≫ d ∧
        ∀ (b : p.Fiber V') (α : aV ⟶ Fiber.fiberInclusion.obj b)
          (β : aU' ⟶ Fiber.fiberInclusion.obj b), p.IsHomLift w α → p.IsHomLift r β →
          u ≫ α = v ≫ β →
          ∃! φ : a ⟶ b, c ≫ Fiber.fiberInclusion.map φ = α ∧
            d ≫ Fiber.fiberInclusion.map φ = β) :
    (fiberSquareRestriction p i q r w hsq).Faithful where
  map_injective {a b} φ φ' h := by
    obtain ⟨aV, aU', aU, c, d, u, v, hc, hd, -, -, huv, hglue⟩ := hFF a
    have h1 : (fiberPullback p w).map φ' = (fiberPullback p w).map φ :=
      congrArg CategoricalPullback.Hom.fst h.symm
    have h2 : (fiberPullback p r).map φ' = (fiberPullback p r).map φ :=
      congrArg CategoricalPullback.Hom.snd h.symm
    have hc' : c ≫ Fiber.fiberInclusion.map φ' = c ≫ Fiber.fiberInclusion.map φ := by
      rw [(fiberPullback_map_eq_iff p w c φ' _).1 rfl,
        (fiberPullback_map_eq_iff p w c φ _).1 rfl,
        h1]
    have hd' : d ≫ Fiber.fiberInclusion.map φ' = d ≫ Fiber.fiberInclusion.map φ := by
      rw [(fiberPullback_map_eq_iff p r d φ' _).1 rfl,
        (fiberPullback_map_eq_iff p r d φ _).1 rfl,
        h2]
    obtain ⟨ψ, -, huniq⟩ := hglue b (c ≫ Fiber.fiberInclusion.map φ)
      (d ≫ Fiber.fiberInclusion.map φ) inferInstance inferInstance
      (by rw [reassoc_of% huv])
    exact (huniq φ ⟨rfl, rfl⟩).trans (huniq φ' ⟨hc', hd'⟩).symm

/-- **Gluing of morphisms along a square makes the comparison functor full.** -/
theorem fiberSquareRestriction_full
    (hFF : ∀ a : p.Fiber V', ∃ (aV aU' aU : 𝒳) (c : aV ⟶ Fiber.fiberInclusion.obj a)
      (d : aU' ⟶ Fiber.fiberInclusion.obj a) (u : aU ⟶ aV) (v : aU ⟶ aU'),
      p.IsCartesian w c ∧ p.IsCartesian r d ∧ p.IsHomLift q u ∧ p.IsHomLift i v ∧
        u ≫ c = v ≫ d ∧
        ∀ (b : p.Fiber V') (α : aV ⟶ Fiber.fiberInclusion.obj b)
          (β : aU' ⟶ Fiber.fiberInclusion.obj b), p.IsHomLift w α → p.IsHomLift r β →
          u ≫ α = v ≫ β →
          ∃! φ : a ⟶ b, c ≫ Fiber.fiberInclusion.map φ = α ∧
            d ≫ Fiber.fiberInclusion.map φ = β) :
    (fiberSquareRestriction p i q r w hsq).Full where
  map_surjective {a b} τ := by
    obtain ⟨aV, aU', aU, c, d, u, v, hc, hd, hu, hv, huv, hglue⟩ := hFF a
    let eV := IsCartesian.domainUniqueUpToIso p w (fiberPullbackHom p w a) c
    let eU' := IsCartesian.domainUniqueUpToIso p r (fiberPullbackHom p r a) d
    have heV : eV.hom ≫ fiberPullbackHom p w a = c := IsCartesian.fac p w _ c
    have heU' : eU'.hom ≫ fiberPullbackHom p r a = d := IsCartesian.fac p r _ d
    let σ : (fiberPullback p w).obj a ⟶ (fiberPullback p w).obj b := τ.fst
    let ρ : (fiberPullback p r).obj a ⟶ (fiberPullback p r).obj b := τ.snd
    let sa := Fiber.fiberInclusion.map ((fiberPullbackSquareIso p i q r w hsq).hom.app a)
    let sb := Fiber.fiberInclusion.map ((fiberPullbackSquareIso p i q r w hsq).hom.app b)
    have hτ : Fiber.fiberInclusion.map ((fiberPullback p q).map σ) ≫ sb =
        sa ≫ Fiber.fiberInclusion.map ((fiberPullback p i).map ρ) := by
      have h0 : (fiberPullback p q).map σ ≫ (fiberPullbackSquareIso p i q r w hsq).hom.app b =
          (fiberPullbackSquareIso p i q r w hsq).hom.app a ≫ (fiberPullback p i).map ρ := τ.w
      simp only [sa, sb, ← Functor.map_comp, h0]
    let α := eV.hom ≫ Fiber.fiberInclusion.map σ ≫ fiberPullbackHom p w b
    let β := eU'.hom ≫ Fiber.fiberInclusion.map ρ ≫ fiberPullbackHom p r b
    let k := IsCartesian.map p q (fiberPullbackHom p q ((fiberPullback p w).obj a)) (u ≫ eV.hom)
    let k' := IsCartesian.map p i (fiberPullbackHom p i ((fiberPullback p r).obj a))
      (v ≫ eU'.hom)
    have hk : k ≫ fiberPullbackHom p q ((fiberPullback p w).obj a) = u ≫ eV.hom :=
      IsCartesian.fac p q _ _
    have hk' : k' ≫ fiberPullbackHom p i ((fiberPullback p r).obj a) = v ≫ eU'.hom :=
      IsCartesian.fac p i _ _
    have hkk : k ≫ sa = k' := by
      apply IsCartesian.ext p (i ≫ r)
        (fiberPullbackHom p i ((fiberPullback p r).obj a) ≫ fiberPullbackHom p r a)
      rw [Category.assoc, fiberInclusion_map_fiberPullbackSquareIso_hom_app, reassoc_of% hk,
        reassoc_of% hk', heV, heU', huv]
    have e3 : sb ≫ fiberPullbackHom p i ((fiberPullback p r).obj b) ≫ fiberPullbackHom p r b =
        fiberPullbackHom p q ((fiberPullback p w).obj b) ≫ fiberPullbackHom p w b :=
      fiberInclusion_map_fiberPullbackSquareIso_hom_app p i q r w hsq b
    have hαβ : u ≫ α = v ≫ β := by
      calc u ≫ α = k ≫ fiberPullbackHom p q ((fiberPullback p w).obj a) ≫
            Fiber.fiberInclusion.map σ ≫ fiberPullbackHom p w b := by
              simp only [α, reassoc_of% hk]
        _ = k ≫ Fiber.fiberInclusion.map ((fiberPullback p q).map σ) ≫ sb ≫
            fiberPullbackHom p i ((fiberPullback p r).obj b) ≫ fiberPullbackHom p r b := by
              rw [← fiberPullback_map_fac_assoc p q σ (fiberPullbackHom p w b), e3]
        _ = k ≫ sa ≫ Fiber.fiberInclusion.map ((fiberPullback p i).map ρ) ≫
            fiberPullbackHom p i ((fiberPullback p r).obj b) ≫ fiberPullbackHom p r b := by
              rw [reassoc_of% hτ]
        _ = v ≫ β := by
              rw [reassoc_of% hkk, fiberPullback_map_fac_assoc p i ρ (fiberPullbackHom p r b),
                reassoc_of% hk']
    obtain ⟨φ, ⟨hφc, hφd⟩, -⟩ := hglue b α β inferInstance inferInstance hαβ
    refine ⟨φ, ?_⟩
    apply CategoricalPullback.hom_ext
    · exact (fiberPullback_map_eq_iff p w c φ σ).2 hφc
    · exact (fiberPullback_map_eq_iff p r d φ ρ).2 hφd

/-- **Gluing of objects along a square makes the comparison functor essentially surjective.** -/
theorem fiberSquareRestriction_essSurj
    (hES : ∀ (xV : p.Fiber V) (xU' : p.Fiber U') (xU : 𝒳)
      (u : xU ⟶ Fiber.fiberInclusion.obj xV) (v : xU ⟶ Fiber.fiberInclusion.obj xU'),
      p.IsCartesian q u → p.IsCartesian i v →
      ∃ (a : p.Fiber V') (μ : Fiber.fiberInclusion.obj xV ⟶ Fiber.fiberInclusion.obj a)
        (ν : Fiber.fiberInclusion.obj xU' ⟶ Fiber.fiberInclusion.obj a),
        p.IsCartesian w μ ∧ p.IsCartesian r ν ∧ u ≫ μ = v ≫ ν) :
    (fiberSquareRestriction p i q r w hsq).EssSurj where
  mem_essImage x := by
    let e := (Fiber.fiberInclusion (p := p) (S := U)).mapIso x.iso
    have he : p.IsHomLift (𝟙 U) e.hom := by
      change p.IsHomLift (𝟙 U) (Fiber.fiberInclusion.map x.iso.hom)
      infer_instance
    have hcart : p.IsCartesian i (e.hom ≫ fiberPullbackHom p i x.snd) :=
      IsCartesian.of_iso_comp p i (fiberPullbackHom p i x.snd) e
    obtain ⟨a, μ, ν, hμ, hν, huv⟩ := hES x.fst x.snd _ (fiberPullbackHom p q x.fst)
      (e.hom ≫ fiberPullbackHom p i x.snd) inferInstance hcart
    let eV := IsCartesian.domainUniqueUpToIso p w μ (fiberPullbackHom p w a)
    let eU' := IsCartesian.domainUniqueUpToIso p r ν (fiberPullbackHom p r a)
    have heV : eV.hom ≫ μ = fiberPullbackHom p w a := IsCartesian.fac p w _ _
    have heU' : eU'.hom ≫ ν = fiberPullbackHom p r a := IsCartesian.fac p r _ _
    let eₗ : (fiberPullback p w).obj a ≅ x.fst := fiberIsoMk p eV inferInstance
    let eᵣ : (fiberPullback p r).obj a ≅ x.snd := fiberIsoMk p eU' inferInstance
    refine ⟨a, ⟨CategoricalPullback.mkIso eₗ eᵣ ?_⟩⟩
    change (fiberPullback p q).map eₗ.hom ≫ x.iso.hom =
      (fiberPullbackSquareIso p i q r w hsq).hom.app a ≫ (fiberPullback p i).map eᵣ.hom
    apply Fiber.hom_ext
    apply IsCartesian.ext p (i ≫ r) (fiberPullbackHom p i x.snd ≫ ν)
    simp only [Functor.map_comp, Category.assoc]
    have hl : Fiber.fiberInclusion.map eₗ.hom ≫ μ = fiberPullbackHom p w a := heV
    have hr : Fiber.fiberInclusion.map eᵣ.hom ≫ ν = fiberPullbackHom p r a := heU'
    simp only [e, Functor.mapIso_hom, Category.assoc] at huv
    rw [← huv, fiberPullback_map_fac_assoc p q eₗ.hom μ, fiberPullback_map_fac_assoc p i eᵣ.hom ν,
      hl, hr, fiberInclusion_map_fiberPullbackSquareIso_hom_app p i q r w hsq a]

/-- **The comparison functor of a square of fibre categories is an equivalence** as soon as
morphisms and objects glue along the square. -/
theorem isEquivalence_fiberSquareRestriction
    (hFF : ∀ a : p.Fiber V', ∃ (aV aU' aU : 𝒳) (c : aV ⟶ Fiber.fiberInclusion.obj a)
      (d : aU' ⟶ Fiber.fiberInclusion.obj a) (u : aU ⟶ aV) (v : aU ⟶ aU'),
      p.IsCartesian w c ∧ p.IsCartesian r d ∧ p.IsHomLift q u ∧ p.IsHomLift i v ∧
        u ≫ c = v ≫ d ∧
        ∀ (b : p.Fiber V') (α : aV ⟶ Fiber.fiberInclusion.obj b)
          (β : aU' ⟶ Fiber.fiberInclusion.obj b), p.IsHomLift w α → p.IsHomLift r β →
          u ≫ α = v ≫ β →
          ∃! φ : a ⟶ b, c ≫ Fiber.fiberInclusion.map φ = α ∧
            d ≫ Fiber.fiberInclusion.map φ = β)
    (hES : ∀ (xV : p.Fiber V) (xU' : p.Fiber U') (xU : 𝒳)
      (u : xU ⟶ Fiber.fiberInclusion.obj xV) (v : xU ⟶ Fiber.fiberInclusion.obj xU'),
      p.IsCartesian q u → p.IsCartesian i v →
      ∃ (a : p.Fiber V') (μ : Fiber.fiberInclusion.obj xV ⟶ Fiber.fiberInclusion.obj a)
        (ν : Fiber.fiberInclusion.obj xU' ⟶ Fiber.fiberInclusion.obj a),
        p.IsCartesian w μ ∧ p.IsCartesian r ν ∧ u ≫ μ = v ≫ ν) :
    (fiberSquareRestriction p i q r w hsq).IsEquivalence where
  faithful := fiberSquareRestriction_faithful p i q r w hsq hFF
  full := fiberSquareRestriction_full p i q r w hsq hFF
  essSurj := fiberSquareRestriction_essSurj p i q r w hsq hES

end Square

end CategoryTheory.Functor

end
