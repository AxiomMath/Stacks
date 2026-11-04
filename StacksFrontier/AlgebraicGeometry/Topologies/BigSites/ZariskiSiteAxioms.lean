module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Topologies.BigSites.ZariskiLimits

/-!
# The small and affine Zariski sites satisfy the site axioms

Let `B` be a big Zariski site containing a scheme `S`. The covering families of the small
Zariski site of `S`, of the big affine site over `S`, and of the small affine site of `S`
satisfy the three site axioms: a singleton isomorphism covers, covering families compose, and
a covering family can be based changed along any morphism.

## Main results

* `AlgebraicGeometry.SmallZariski.isSite` — the small Zariski coverings form a site.
* `AlgebraicGeometry.BigAffineZariski.isSite` — the standard coverings of affines over `S`
  form a site.
* `AlgebraicGeometry.SmallAffineZariski.isSite` — the standard coverings of affine opens of
  `S` form a site.

## Implementation notes

The three statements are about `CategoryTheory.IsSite` for the covering-family predicates
themselves rather than for the Grothendieck topologies they generate; the site axioms for the
big Zariski site are already part of its definition.

In each case the first two axioms are inherited from the big site, and the base-change axiom
is proved by forming the fibre product there and checking that it still lies in the full
subcategory: the base change of an open immersion is an open immersion, and the base change
of an affine is affine. For the two affine sites one must in addition check that the
*standard* form of a covering — a finite family of basic opens — is preserved, which is what
the four private lemmas on `basicOpen` data do: `standardZariski_comp_data` for composition,
`standardZariski_pullback_data` for base change, and `singletonStandardData` and
`bindStandardData` to assemble the data in the shape the covering predicate expects.

## References

* [Stacks Project, Tag 020U](https://stacks.math.columbia.edu/tag/020U)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

namespace AlgebraicGeometry

private lemma standardZariski_comp_data {T : Scheme.{u}} [IsAffine T]
    {I : Type*} {X : I → Scheme.{u}} (f : ∀ i, X i ⟶ T)
    {J : I → Type*} {Y : ∀ i, J i → Scheme.{u}} (g : ∀ i j, Y i j ⟶ X i)
    (hE : Finite I ∧ ∀ i, ∃ r : Γ(T, ⊤), ∃ e : X i ≅ (T.basicOpen r).toScheme,
      f i = e.hom ≫ (T.basicOpen r).ι)
    (hF : ∀ i, Finite (J i) ∧ ∀ j, ∃ r : Γ(X i, ⊤),
      ∃ e : Y i j ≅ ((X i).basicOpen r).toScheme,
        g i j = e.hom ≫ ((X i).basicOpen r).ι) :
    Finite (Σ i : I, J i) ∧ ∀ (ij : Σ i : I, J i), ∃ r : Γ(T, ⊤),
      ∃ e : Y ij.1 ij.2 ≅ (T.basicOpen r).toScheme,
        g ij.1 ij.2 ≫ f ij.1 = e.hom ≫ (T.basicOpen r).ι := by
  let : Finite I := hE.1
  have : ∀ i, Finite (J i) := fun i => (hF i).1
  constructor
  · infer_instance
  · intro ij
    rcases hE.2 ij.1 with ⟨r, e, he⟩
    rcases (hF ij.1).2 ij.2 with ⟨s, e', he'⟩
    let U := (T.basicOpen r).toScheme
    let V := X ij.1
    let q₁ : Y ij.1 ij.2 ⟶ V := e'.hom ≫ (V.basicOpen s).ι
    let q₂ : Y ij.1 ij.2 ⟶ U := q₁ ≫ e.hom
    let q : Y ij.1 ij.2 ⟶ T := q₂ ≫ (T.basicOpen r).ι
    have hE_image : e.hom ''ᵁ ⊤ = ⊤ := by
      rw [e.hom.image_top_eq_opensRange, Scheme.Hom.opensRange_of_isIso]
    let s₁ : Γ(U, ⊤) :=
      U.presheaf.map (eqToHom hE_image.symm).op ((e.hom.appIso ⊤).inv s)
    have hRange : (T.basicOpen r).ι.opensRange = T.basicOpen r := by simp
    have hRangeImage : (T.basicOpen r).ι ''ᵁ ⊤ = T.basicOpen r :=
      (T.basicOpen r).ι.image_top_eq_opensRange.trans hRange
    let s₂ : Γ(T, T.basicOpen r) :=
      T.presheaf.map (eqToHom hRangeImage.symm).op
        ((ConcreteCategory.hom ((T.basicOpen r).ι.appIso ⊤).inv) s₁)
    obtain ⟨r', hr'⟩ := (isAffineOpen_top T).basicOpen_basicOpen_is_basicOpen r s₂
    have hrange : q.opensRange = T.basicOpen r' := by
      calc
        q.opensRange = (T.basicOpen r).ι ''ᵁ q₂.opensRange :=
          Scheme.Hom.opensRange_comp q₂ (T.basicOpen r).ι
        _ = (T.basicOpen r).ι ''ᵁ (e.hom ''ᵁ V.basicOpen s) := by
          show (T.basicOpen r).ι ''ᵁ (q₁ ≫ e.hom).opensRange = _
          rw [Scheme.Hom.opensRange_comp]
          have hq₁ : q₁.opensRange = V.basicOpen s := by
            simp [q₁, Scheme.Hom.opensRange_comp_of_isIso]
          rw [hq₁]
        _ = (T.basicOpen r).ι ''ᵁ U.basicOpen s₁ := by
          rw [Scheme.image_basicOpen]
          exact congrArg (fun W : U.Opens => (T.basicOpen r).ι ''ᵁ W)
            (Scheme.basicOpen_res_eq U ((e.hom.appIso ⊤).inv s)
              (eqToHom hE_image.symm).op).symm
        _ = T.basicOpen s₂ := by
          rw [Scheme.image_basicOpen]
          show T.basicOpen
            ((ConcreteCategory.hom ((T.basicOpen r).ι.appIso ⊤).inv) s₁) =
              T.basicOpen s₂
          rw [show s₂ = T.presheaf.map (eqToHom hRangeImage.symm).op
              ((ConcreteCategory.hom ((T.basicOpen r).ι.appIso ⊤).inv) s₁) by rfl]
          exact (Scheme.basicOpen_res_eq T
            ((ConcreteCategory.hom ((T.basicOpen r).ι.appIso ⊤).inv) s₁)
            (eqToHom hRangeImage.symm).op).symm
        _ = T.basicOpen r' := hr'.symm
    have hrange' : Set.range q = Set.range (T.basicOpen r').ι := by
      simpa only [Scheme.Hom.coe_opensRange, Scheme.Opens.range_ι] using
        congrArg (fun U : T.Opens => (U : Set T)) hrange
    let e'' := IsOpenImmersion.isoOfRangeEq q (T.basicOpen r').ι hrange'
    refine ⟨r', e'', ?_⟩
    calc
      g ij.1 ij.2 ≫ f ij.1 = q := by
        simp [q, q₂, q₁, V, he', he, Category.assoc]
      _ = e''.hom ≫ (T.basicOpen r').ι := (IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _).symm

private lemma standardZariski_pullback_data {T V : Scheme.{u}}
    {I : Type*} {X : I → Scheme.{u}} (f : ∀ i, X i ⟶ T)
    (hE : Finite I ∧ ∀ i, ∃ r : Γ(T, ⊤), ∃ e : X i ≅ (T.basicOpen r).toScheme,
      f i = e.hom ≫ (T.basicOpen r).ι)
    (g : V ⟶ T) {P : I → Scheme.{u}} (p₁ : ∀ i, P i ⟶ X i)
    (p₂ : ∀ i, P i ⟶ V) (hp : ∀ i, IsPullback (p₁ i) (p₂ i) (f i) g) :
    Finite I ∧ ∀ i, ∃ r : Γ(V, ⊤), ∃ e : P i ≅ (V.basicOpen r).toScheme,
      p₂ i = e.hom ≫ (V.basicOpen r).ι := by
  have : Finite I := hE.1
  refine ⟨inferInstance, fun i => ?_⟩
  obtain ⟨r, e, he⟩ := hE.2 i
  let r' := g.appTop r
  have : IsOpenImmersion (f i) := by rw [he]; infer_instance
  have : IsOpenImmersion (p₂ i) :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback (hp i) inferInstance
  have hbase : (f i).opensRange = T.basicOpen r := by
    calc
      _ = ((T.basicOpen r).ι).opensRange := by
        simpa only [he] using
          Scheme.Hom.opensRange_comp_of_isIso e.hom (T.basicOpen r).ι
      _ = _ := by simp
  have hpRange : (p₂ i).opensRange = V.basicOpen r' := by
    calc
      (p₂ i).opensRange =
          ((hp i).isoPullback.hom ≫ Limits.pullback.snd (f i) g).opensRange := by
            simp only [(hp i).isoPullback_hom_snd]
      _ = (Limits.pullback.snd (f i) g).opensRange :=
        Scheme.Hom.opensRange_comp_of_isIso _ _
      _ = g ⁻¹ᵁ (f i).opensRange := Scheme.Hom.opensRange_pullbackSnd _ _
      _ = g ⁻¹ᵁ T.basicOpen r := by rw [hbase]
      _ = V.basicOpen r' := Scheme.preimage_basicOpen_top _ _
  have hpRange' : Set.range (p₂ i) = Set.range (V.basicOpen r').ι := by
    simpa only [Scheme.Hom.coe_opensRange, Scheme.Opens.range_ι] using
      congrArg (fun U : V.Opens => (U : Set V)) hpRange
  let e' := IsOpenImmersion.isoOfRangeEq (p₂ i) (V.basicOpen r').ι hpRange'
  exact ⟨r', e', (IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _).symm⟩

/-- A commutative square of morphisms over `U` has equal composites to the base `S`. -/
private lemma comp_eq_of_square {C : Type*} [Category C] {P X V U S : C} {p₁ : P ⟶ X} {p₂ : P ⟶ V}
    {f : X ⟶ U} {g : V ⟶ U} {x : X ⟶ S} {u : U ⟶ S} {v : V ⟶ S}
    (hp : p₁ ≫ f = p₂ ≫ g) (hf : f ≫ u = x) (hg : g ≫ u = v) : p₁ ≫ x = p₂ ≫ v := by
  rw [← hf, ← hg, ← Category.assoc, hp, Category.assoc]

private lemma finishStandardCover (B : AlgebraicGeometry.BigZariskiSite.{u})
    {C : Type*} [Category C] (K : C ⥤ B.Schemes) (E : Covering C)
    [IsAffine ((K ⋙ B.inclusion).obj E.1)]
    (hB : B.IsCovering ⟨K.obj E.1, E.2.map K⟩)
    (hdata : Finite E.2.I₀ ∧ ∀ i,
      ∃ r : Γ((K ⋙ B.inclusion).obj E.1, ⊤),
      ∃ e : (K ⋙ B.inclusion).obj (E.2.X i) ≅
        (((K ⋙ B.inclusion).obj E.1).basicOpen r).toScheme,
        (K ⋙ B.inclusion).map (E.2.f i) =
          e.hom ≫ (((K ⋙ B.inclusion).obj E.1).basicOpen r).ι) :
    B.IsCovering ⟨K.obj E.1, E.2.map K⟩ ∧
      ∃ hZ : (E.2.map (K ⋙ B.inclusion)).presieve₀ ∈
        Scheme.zariskiPrecoverage ((K ⋙ B.inclusion).obj E.1),
        AlgebraicGeometry.IsStandardZariskiCovering
          (⟨E.2.map (K ⋙ B.inclusion), hZ⟩ :
            ((K ⋙ B.inclusion).obj E.1).Cover Scheme.zariskiPrecoverage) :=
  ⟨hB, hB.1, by simpa [AlgebraicGeometry.IsStandardZariskiCovering,
    PreZeroHypercover.map, Functor.comp_map] using hdata⟩

private lemma singletonStandardData {C : Type*} [Category C] (G : C ⥤ Scheme.{u})
    (U V : C) (f : V ⟶ U) [IsIso f] [IsAffine (G.obj U)] :
    Finite (PreZeroHypercover.singleton f).I₀ ∧ ∀ i,
      ∃ r : Γ(G.obj U, ⊤), ∃ e : G.obj ((PreZeroHypercover.singleton f).X i) ≅
        ((G.obj U).basicOpen r).toScheme,
        G.map ((PreZeroHypercover.singleton f).f i) =
          e.hom ≫ ((G.obj U).basicOpen r).ι := by
  let T := G.obj U
  have : IsIso ((T.basicOpen (1 : Γ(T, ⊤))).ι) :=
    AlgebraicGeometry.isIso_of_isOpenImmersion_of_opensRange_eq_top _ (by simp)
  let e : G.obj V ≅ (T.basicOpen (1 : Γ(T, ⊤))).toScheme :=
    (asIso (G.map f)) ≪≫ (asIso (T.basicOpen (1 : Γ(T, ⊤))).ι).symm
  refine ⟨inferInstance, fun i => ⟨1, e, ?_⟩⟩
  simp [e, T, PreZeroHypercover.singleton]

private lemma standardCoverData {C : Type*} [Category C] (G : C ⥤ Scheme.{u})
    (E : Covering C) [IsAffine (G.obj E.1)]
    (h : ∃ hZ : (E.2.map G).presieve₀ ∈ Scheme.zariskiPrecoverage (G.obj E.1),
      AlgebraicGeometry.IsStandardZariskiCovering
        (⟨E.2.map G, hZ⟩ : (G.obj E.1).Cover Scheme.zariskiPrecoverage)) :
    Finite E.2.I₀ ∧ ∀ i, ∃ r : Γ(G.obj E.1, ⊤),
      ∃ e : G.obj (E.2.X i) ≅ ((G.obj E.1).basicOpen r).toScheme,
        G.map (E.2.f i) = e.hom ≫ ((G.obj E.1).basicOpen r).ι := by
  obtain ⟨hZ, h⟩ := h
  simpa [AlgebraicGeometry.IsStandardZariskiCovering, PreZeroHypercover.map] using h

private lemma bindStandardData {C : Type*} [Category C] (G : C ⥤ Scheme.{u})
    (E : Covering C) (F : E.2.I₀ → Covering C) (h : ∀ i, (F i).1 = E.2.X i)
    [IsAffine (G.obj E.1)]
    (hE : Finite E.2.I₀ ∧ ∀ i, ∃ r : Γ(G.obj E.1, ⊤),
      ∃ e : G.obj (E.2.X i) ≅ ((G.obj E.1).basicOpen r).toScheme,
        G.map (E.2.f i) = e.hom ≫ ((G.obj E.1).basicOpen r).ι)
    (hF : ∀ i, Finite (F i).2.I₀ ∧ ∀ j,
      ∃ r : Γ(G.obj (F i).1, ⊤),
      ∃ e : G.obj ((F i).2.X j) ≅ ((G.obj (F i).1).basicOpen r).toScheme,
        G.map ((F i).2.f j) = e.hom ≫ ((G.obj (F i).1).basicOpen r).ι) :
    let Ecomp : Covering C :=
      ⟨E.1, E.2.bind fun i => (F i).2.pushforward (eqToHom (h i))⟩
    Finite Ecomp.2.I₀ ∧ ∀ i, ∃ r : Γ(G.obj Ecomp.1, ⊤),
      ∃ e : G.obj (Ecomp.2.X i) ≅ ((G.obj Ecomp.1).basicOpen r).toScheme,
        G.map (Ecomp.2.f i) = e.hom ≫ ((G.obj Ecomp.1).basicOpen r).ι := by
  have hcomp := standardZariski_comp_data
    (T := G.obj E.1) (X := fun i => G.obj (F i).1)
    (f := fun i => G.map (eqToHom (h i)) ≫ G.map (E.2.f i))
    (Y := fun i j => G.obj ((F i).2.X j))
    (g := fun i j => G.map ((F i).2.f j))
    ⟨hE.1, fun i => by
      obtain ⟨r, e, he⟩ := hE.2 i
      refine ⟨r, (asIso (G.map (eqToHom (h i)))) ≪≫ e, ?_⟩
      simp [he]⟩ hF
  simpa [PreZeroHypercover.bind, PreZeroHypercover.pushforward,
    PreZeroHypercover.map, Functor.map_comp, eqToHom_map, Category.assoc] using hcomp

namespace SmallZariski

/-- Zariski coverings of schemes open in `S` satisfy the site axioms. -/
@[stacks 020U "small Zariski site"]
public theorem isSite (B : AlgebraicGeometry.BigZariskiSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) : IsSite (AlgebraicGeometry.SmallZariski.IsCovering B S hS) :=
  by
    let K : AlgebraicGeometry.SmallZariski B S hS ⥤ B.Schemes :=
      AlgebraicGeometry.SmallZariski.inclusion B S hS ⋙
        AlgebraicGeometry.BigZariskiOver.inclusion B S hS
    refine ⟨?_, ?_, ?_⟩
    · intro U V f hf
      show B.IsCovering ⟨K.obj U, (PreZeroHypercover.singleton f).map K⟩
      have hmap : (PreZeroHypercover.singleton f).map K =
          PreZeroHypercover.singleton (K.map f) := by
        exact PreZeroHypercover.ext rfl HEq.rfl HEq.rfl
      rw [hmap]
      exact B.coverings_isSite.1 (K.map f)
    · intro E hE F hF htargets
      change B.IsCovering ⟨K.obj E.1, E.2.map K⟩ at hE
      change ∀ i, B.IsCovering ⟨K.obj (F i).1, (F i).2.map K⟩ at hF
      show B.IsCovering ⟨K.obj E.1,
        (E.2.bind fun i => (F i).2.pushforward (eqToHom (htargets i))).map K⟩
      have hcomp := B.coverings_isSite.2.1 ⟨K.obj E.1, E.2.map K⟩ hE
        (fun i => ⟨K.obj (F i).1, (F i).2.map K⟩) hF
        (fun i => congrArg K.obj (htargets i))
      simpa [AlgebraicGeometry.BigZariskiSite.IsCovering, PreZeroHypercover.map,
        PreZeroHypercover.bind, PreZeroHypercover.pushforward, Functor.map_comp, eqToHom_map,
        Category.assoc] using hcomp
    · intro E hE V g
      let E₀ : Covering B.Schemes := ⟨K.obj E.1, E.2.map K⟩
      obtain ⟨P, p₁, p₂, hp, hcov⟩ :=
        B.coverings_isSite.2.2 E₀ hE V.obj.left g.hom.left
      dsimp [E₀, PreZeroHypercover.map] at P p₁ p₂ hp hcov
      let Q (i : E.2.I₀) : AlgebraicGeometry.SmallZariski B S hS :=
        ⟨Over.mk (p₂ i ≫ V.obj.hom), by
          show IsOpenImmersion (B.inclusion.map (p₂ i ≫ V.obj.hom))
          have hUi : IsOpenImmersion (B.inclusion.map (E.2.f i).hom.left) := by
            let : IsOpenImmersion (B.inclusion.map E.1.obj.hom) := E.1.property
            let : IsOpenImmersion (B.inclusion.map (E.2.f i).hom.left ≫
                B.inclusion.map E.1.obj.hom) := by
              have hcomp : (E.2.f i).hom.left ≫ E.1.obj.hom = (E.2.X i).obj.hom :=
                (E.2.f i).hom.w
              rw [← Functor.map_comp, hcomp]
              exact (E.2.X i).property
            exact IsOpenImmersion.of_comp (B.inclusion.map (E.2.f i).hom.left)
              (B.inclusion.map E.1.obj.hom)
          have hpb' : IsPullback (B.inclusion.map (p₁ i))
              (B.inclusion.map (p₂ i)) (B.inclusion.map (E.2.f i).hom.left)
              (B.inclusion.map g.hom.left) := by
            exact Functor.map_isPullback B.inclusion (hp i)
          have : IsOpenImmersion (B.inclusion.map (p₂ i)) := by
            exact MorphismProperty.IsStableUnderBaseChange.of_isPullback hpb' hUi
          rw [Functor.map_comp]
          exact IsOpenImmersion.comp _ _⟩
      let q₁ (i : E.2.I₀) : Q i ⟶ E.2.X i :=
        ObjectProperty.homMk (Over.homMk (p₁ i)
          (by exact comp_eq_of_square (hp i).w (E.2.f i).hom.w g.hom.w))
      let q₂ (i : E.2.I₀) : Q i ⟶ V :=
        ObjectProperty.homMk (Over.homMk (p₂ i) (by rfl))
      refine ⟨Q, q₁, q₂, ?_, ?_⟩
      · intro i
        have hw : q₁ i ≫ E.2.f i = q₂ i ≫ g :=
          (AlgebraicGeometry.SmallZariski.inclusion B S hS).map_injective
            (Over.OverMorphism.ext (hp i).w)
        apply IsPullback.of_map (AlgebraicGeometry.SmallZariski.inclusion B S hS) hw
        apply IsPullback.of_map (AlgebraicGeometry.BigZariskiOver.inclusion B S hS)
        · exact Over.OverMorphism.ext (hp i).w
        · exact hp i
      · show B.IsCovering
          ⟨K.obj V, (PreZeroHypercover.mk _ Q q₂).map K⟩
        simpa [Q, q₂, K, PreZeroHypercover.map] using hcov

end SmallZariski

namespace BigAffineZariski

/-- Standard Zariski coverings of affine schemes over `S` satisfy the site axioms. -/
@[stacks 020U "big affine Zariski site"]
public theorem isSite (B : AlgebraicGeometry.BigZariskiSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) : IsSite (AlgebraicGeometry.BigAffineZariski.IsCovering B S hS) := by
  let K : AlgebraicGeometry.BigAffineZariski B S hS ⥤ B.Schemes :=
    AlgebraicGeometry.BigAffineZariski.inclusion B S hS ⋙
      AlgebraicGeometry.BigZariskiOver.inclusion B S hS
  let G : AlgebraicGeometry.BigAffineZariski B S hS ⥤ Scheme.{u} :=
    AlgebraicGeometry.BigAffineZariski.toScheme B S hS
  have finishCover (E : Covering (AlgebraicGeometry.BigAffineZariski B S hS))
      (hB : B.IsCovering ⟨K.obj E.1, E.2.map K⟩)
      (hdata : Finite E.2.I₀ ∧ ∀ i, ∃ r : Γ(G.obj E.1, ⊤),
        ∃ e : (G.obj (E.2.X i)) ≅ ((G.obj E.1).basicOpen r).toScheme,
          G.map (E.2.f i) = e.hom ≫ ((G.obj E.1).basicOpen r).ι) :
      AlgebraicGeometry.BigAffineZariski.IsCovering B S hS E := by
    show B.IsCovering ⟨K.obj E.1, E.2.map K⟩ ∧ _
    let : IsAffine ((K ⋙ B.inclusion).obj E.1) := E.1.property
    exact finishStandardCover B K E hB hdata
  refine ⟨?_, ?_, ?_⟩
  · intro U V f hf
    let E : Covering (AlgebraicGeometry.BigAffineZariski B S hS) :=
      ⟨U, PreZeroHypercover.singleton f⟩
    have hB : B.IsCovering ⟨K.obj U, E.2.map K⟩ := by
      have hmap : E.2.map K = PreZeroHypercover.singleton (K.map f) := by
        exact PreZeroHypercover.ext rfl HEq.rfl HEq.rfl
      rw [hmap]
      let : IsIso (K.map f) := Functor.map_isIso K f
      exact B.coverings_isSite.1 (K.map f)
    let : IsAffine (G.obj U) := U.property
    exact finishCover E hB (singletonStandardData G U V f)
  · intro E hE F hF h
    let : IsAffine (G.obj E.1) := E.1.property
    obtain ⟨hBE, hstdE⟩ := hE
    have hdataE := standardCoverData G E hstdE
    have hBF (i : E.2.I₀) : B.IsCovering ⟨K.obj (F i).1, (F i).2.map K⟩ :=
      (hF i).1
    have hstdF (i : E.2.I₀) := by
      let : IsAffine (G.obj (F i).1) := (F i).1.property
      exact standardCoverData G (F i) (hF i).2
    have hBcomp := B.coverings_isSite.2.1 ⟨K.obj E.1, E.2.map K⟩ hBE
      (fun i => ⟨K.obj (F i).1, (F i).2.map K⟩) hBF
      (fun i => congrArg K.obj (h i))
    let Ecomp : Covering (AlgebraicGeometry.BigAffineZariski B S hS) :=
      ⟨E.1, E.2.bind fun i => (F i).2.pushforward (eqToHom (h i))⟩
    have hBcomp' : B.IsCovering ⟨K.obj Ecomp.1, Ecomp.2.map K⟩ := by
      simpa [Ecomp, PreZeroHypercover.bind, PreZeroHypercover.pushforward,
        PreZeroHypercover.map, Functor.map_comp, eqToHom_map, Category.assoc] using hBcomp
    exact finishCover Ecomp hBcomp' (bindStandardData G E F h hdataE hstdF)
  · intro E hE V g
    let : IsAffine (G.obj E.1) := E.1.property
    obtain ⟨hBE, hstdE⟩ := hE
    have hdataE := standardCoverData G E hstdE
    obtain ⟨P, p₁, p₂, hp, hBcov⟩ := B.coverings_isSite.2.2
      ⟨K.obj E.1, E.2.map K⟩ hBE (K.obj V) (K.map g)
    let Psch (i : E.2.I₀) := B.inclusion.obj (P i)
    have hpSch (i : E.2.I₀) : IsPullback (B.inclusion.map (p₁ i))
        (B.inclusion.map (p₂ i)) (G.map (E.2.f i)) (G.map g) :=
      Functor.map_isPullback B.inclusion (hp i)
    have hdataP := standardZariski_pullback_data
      (T := G.obj E.1) (V := G.obj V) (X := fun i => G.obj (E.2.X i))
      (f := fun i => G.map (E.2.f i)) hdataE (G.map g)
      (P := Psch) (p₁ := fun i => B.inclusion.map (p₁ i))
      (p₂ := fun i => B.inclusion.map (p₂ i)) hpSch
    let Q (i : E.2.I₀) : AlgebraicGeometry.BigAffineZariski B S hS :=
      ⟨Over.mk (p₂ i ≫ V.obj.hom), by
        rcases hdataP.2 i with ⟨r, e, he⟩
        let : IsAffine ((G.obj V).basicOpen r).toScheme := inferInstance
        exact IsAffine.of_isIso e.hom⟩
    let q₁ (i : E.2.I₀) : Q i ⟶ E.2.X i :=
      ObjectProperty.homMk <| Over.homMk (U := (Q i).obj) (V := (E.2.X i).obj) (p₁ i)
        (by exact comp_eq_of_square (hp i).w (E.2.f i).hom.w g.hom.w)
    let q₂ (i : E.2.I₀) : Q i ⟶ V :=
      ObjectProperty.homMk <| Over.homMk (U := (Q i).obj) (V := V.obj) (p₂ i) rfl
    refine ⟨Q, q₁, q₂, ?_, ?_⟩
    · intro i
      have hw : q₁ i ≫ E.2.f i = q₂ i ≫ g :=
        (AlgebraicGeometry.BigAffineZariski.inclusion B S hS).map_injective
          (Over.OverMorphism.ext (hp i).w)
      apply IsPullback.of_map (AlgebraicGeometry.BigAffineZariski.inclusion B S hS) hw
      apply IsPullback.of_map (AlgebraicGeometry.BigZariskiOver.inclusion B S hS)
      · exact Over.OverMorphism.ext (hp i).w
      · exact hp i
    · have hdataQ : Finite E.2.I₀ ∧ ∀ i,
          ∃ r : Γ(G.obj V, ⊤),
            ∃ e : G.obj (Q i) ≅ ((G.obj V).basicOpen r).toScheme,
              G.map (q₂ i) = e.hom ≫ ((G.obj V).basicOpen r).ι := by
        refine ⟨hdataP.1, ?_⟩
        intro i
        rcases hdataP.2 i with ⟨r, e, he⟩
        refine ⟨r, e, ?_⟩
        simpa [q₂, Q, G, AlgebraicGeometry.BigAffineZariski.toScheme,
          AlgebraicGeometry.BigAffineZariski.inclusion,
          AlgebraicGeometry.BigZariskiOver.toScheme,
          AlgebraicGeometry.BigZariskiOver.inclusion] using he
      exact finishCover ⟨V, ⟨E.2.I₀, Q, q₂⟩⟩ hBcov hdataQ

end BigAffineZariski

namespace SmallAffineZariski

/-- Standard Zariski coverings of affine opens of `S` satisfy the site axioms. -/
@[stacks 020U "small affine Zariski site"]
public theorem isSite (B : AlgebraicGeometry.BigZariskiSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) : IsSite (AlgebraicGeometry.SmallAffineZariski.IsCovering B S hS) :=
  by
    let H : AlgebraicGeometry.SmallAffineZariski B S hS ⥤
        AlgebraicGeometry.SmallZariski B S hS :=
      AlgebraicGeometry.SmallAffineZariski.inclusion B S hS
    let K : AlgebraicGeometry.SmallAffineZariski B S hS ⥤ B.Schemes :=
      H ⋙ AlgebraicGeometry.SmallZariski.inclusion B S hS ⋙
        AlgebraicGeometry.BigZariskiOver.inclusion B S hS
    let Gsmall : AlgebraicGeometry.SmallZariski B S hS ⥤ Scheme.{u} :=
      AlgebraicGeometry.SmallZariski.toScheme B S hS
    let G : AlgebraicGeometry.SmallAffineZariski B S hS ⥤ Scheme.{u} :=
      AlgebraicGeometry.SmallAffineZariski.toScheme B S hS
    have finishCover (E : Covering (AlgebraicGeometry.SmallAffineZariski B S hS))
        (hB : B.IsCovering ⟨K.obj E.1, E.2.map K⟩)
        (hdata : Finite E.2.I₀ ∧ ∀ i, ∃ r : Γ(G.obj E.1, ⊤),
          ∃ e : G.obj (E.2.X i) ≅ ((G.obj E.1).basicOpen r).toScheme,
            G.map (E.2.f i) = e.hom ≫ ((G.obj E.1).basicOpen r).ι) :
        AlgebraicGeometry.SmallAffineZariski.IsCovering B S hS E := by
      show B.IsCovering ⟨K.obj E.1, E.2.map K⟩ ∧ _
      let : IsAffine ((K ⋙ B.inclusion).obj E.1) := E.1.property
      exact finishStandardCover B K E hB hdata
    refine ⟨?_, ?_, ?_⟩
    · intro U V f hf
      let E : Covering (AlgebraicGeometry.SmallAffineZariski B S hS) :=
        ⟨U, PreZeroHypercover.singleton f⟩
      have hsmall : AlgebraicGeometry.SmallZariski.IsCovering B S hS
          ⟨H.obj U, (PreZeroHypercover.singleton f).map H⟩ := by
        let : IsIso (H.map f) := Functor.map_isIso H f
        exact (SmallZariski.isSite B S hS).1 (H.map f)
      have hB : B.IsCovering ⟨K.obj U, E.2.map K⟩ := by
        simpa [AlgebraicGeometry.SmallZariski.IsCovering,
          AlgebraicGeometry.BigZariskiOver.IsCovering, E, PreZeroHypercover.map,
          Functor.comp_map, H, K] using hsmall
      let : IsAffine (G.obj U) := U.property
      exact finishCover E hB (singletonStandardData G U V f)
    · intro E hE F hF h
      let : IsAffine (G.obj E.1) := E.1.property
      obtain ⟨hBE, hstdE⟩ := hE
      have hdataE := standardCoverData G E hstdE
      have hBEsmall : AlgebraicGeometry.SmallZariski.IsCovering B S hS
          ⟨H.obj E.1, E.2.map H⟩ := by
        simpa [AlgebraicGeometry.SmallZariski.IsCovering,
          AlgebraicGeometry.BigZariskiOver.IsCovering, PreZeroHypercover.map, Functor.comp_map,
          H, K] using hBE
      have hBF (i : E.2.I₀) : AlgebraicGeometry.SmallZariski.IsCovering B S hS
          ⟨H.obj (F i).1, (F i).2.map H⟩ := by
        exact (hF i).1
      have hstdF (i : E.2.I₀) := by
        let : IsAffine (G.obj (F i).1) := (F i).1.property
        exact standardCoverData G (F i) (hF i).2
      have hsmallComp := (SmallZariski.isSite B S hS).2.1
          ⟨H.obj E.1, E.2.map H⟩ hBEsmall
        (fun i => ⟨H.obj (F i).1, (F i).2.map H⟩) hBF
        (fun i => congrArg H.obj (h i))
      have hBcomp : B.IsCovering ⟨K.obj E.1,
          (E.2.bind fun i => (F i).2.pushforward (eqToHom (h i))).map K⟩ := by
        simpa [AlgebraicGeometry.SmallZariski.IsCovering,
          AlgebraicGeometry.BigZariskiOver.IsCovering, PreZeroHypercover.map,
          PreZeroHypercover.bind, PreZeroHypercover.pushforward,
          Functor.map_comp, Functor.comp_map, eqToHom_map, Category.assoc, H, K] using
          hsmallComp
      let Ecomp : Covering (AlgebraicGeometry.SmallAffineZariski B S hS) :=
        ⟨E.1, E.2.bind fun i => (F i).2.pushforward (eqToHom (h i))⟩
      exact finishCover Ecomp hBcomp (bindStandardData G E F h hdataE hstdF)
    · intro E hE V g
      let : IsAffine (G.obj E.1) := E.1.property
      obtain ⟨hBE, hstdE⟩ := hE
      have hdataE := standardCoverData G E hstdE
      let E₀ : Covering (AlgebraicGeometry.SmallZariski B S hS) :=
        ⟨H.obj E.1, E.2.map H⟩
      have hBEsmall : AlgebraicGeometry.SmallZariski.IsCovering B S hS E₀ := by
        show B.IsCovering ⟨K.obj E.1, E.2.map K⟩
        exact hBE
      obtain ⟨P, p₁, p₂, hp, hsmallCov⟩ :=
        (SmallZariski.isSite B S hS).2.2 E₀ hBEsmall (H.obj V) (H.map g)
      have hpScheme (i : E.2.I₀) : IsPullback
          (Gsmall.map (p₁ i)) (Gsmall.map (p₂ i))
          (Gsmall.map ((E.2.map H).f i)) (Gsmall.map (H.map g)) :=
        Functor.map_isPullback Gsmall (hp i)
      have hdataP := standardZariski_pullback_data
        (T := G.obj E.1) (V := G.obj V) (X := fun i => G.obj (E.2.X i))
        (f := fun i => G.map (E.2.f i)) hdataE (G.map g)
        (P := fun i => Gsmall.obj (P i))
        (p₁ := fun i => Gsmall.map (p₁ i)) (p₂ := fun i => Gsmall.map (p₂ i))
        (hp := by simpa [E₀, PreZeroHypercover.map, G, Gsmall, H] using hpScheme)
      let Q (i : E.2.I₀) : AlgebraicGeometry.SmallAffineZariski B S hS :=
        ⟨P i, by
          rcases hdataP.2 i with ⟨r, e, he⟩
          let : IsAffine ((G.obj V).basicOpen r).toScheme := inferInstance
          exact IsAffine.of_isIso e.hom⟩
      let q₁ (i : E.2.I₀) : Q i ⟶ E.2.X i :=
        ObjectProperty.homMk (p₁ i)
      let q₂ (i : E.2.I₀) : Q i ⟶ V :=
        ObjectProperty.homMk (p₂ i)
      refine ⟨Q, q₁, q₂, ?_, ?_⟩
      · intro i
        have hw : q₁ i ≫ E.2.f i = q₂ i ≫ g :=
          (AlgebraicGeometry.SmallAffineZariski.inclusion B S hS).map_injective ((hp i).w)
        apply IsPullback.of_map (AlgebraicGeometry.SmallAffineZariski.inclusion B S hS) hw
        exact hp i
      · have hBcov : B.IsCovering
            ⟨K.obj V, ((PreZeroHypercover.mk _ Q q₂).map K)⟩ := by
          simpa [E₀, AlgebraicGeometry.SmallZariski.IsCovering,
            AlgebraicGeometry.BigZariskiOver.IsCovering, PreZeroHypercover.map,
            Functor.comp_map, H, K, Q, q₂] using hsmallCov
        have hdataQ : Finite E.2.I₀ ∧ ∀ i,
            ∃ r : Γ(G.obj V, ⊤),
              ∃ e : G.obj (Q i) ≅ ((G.obj V).basicOpen r).toScheme,
                G.map (q₂ i) = e.hom ≫ ((G.obj V).basicOpen r).ι := by
          refine ⟨hdataP.1, ?_⟩
          intro i
          rcases hdataP.2 i with ⟨r, e, he⟩
          refine ⟨r, e, ?_⟩
          simpa [q₂, Q, G, Gsmall, AlgebraicGeometry.SmallAffineZariski.toScheme,
            AlgebraicGeometry.SmallAffineZariski.inclusion,
            AlgebraicGeometry.SmallZariski.toScheme, AlgebraicGeometry.SmallZariski.inclusion,
            AlgebraicGeometry.BigZariskiOver.toScheme,
            AlgebraicGeometry.BigZariskiOver.inclusion] using he
        exact finishCover ⟨V, ⟨E.2.I₀, Q, q₂⟩⟩ hBcov hdataQ

end SmallAffineZariski


end AlgebraicGeometry
