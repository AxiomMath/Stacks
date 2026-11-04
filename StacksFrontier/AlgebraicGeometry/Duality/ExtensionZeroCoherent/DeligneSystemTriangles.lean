module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Homology.DerivedCategory.EssentiallyConstant
public import StacksFrontier.AlgebraicGeometry.Duality.ExtensionZeroCoherent.ExtensionByZeroFunctor
public import StacksFrontier.AlgebraicGeometry.Duality.ExtensionZeroCoherent.SequentialProIsomorphism
public import StacksFrontier.RingTheory.Module.AdicSystem.Homology

/-!
# Two-out-of-three for Deligne systems

Let `j : U → X` be an open immersion of Noetherian schemes. A *Deligne system* on `X` is an
inverse system in `D^b_{Coh}(𝒪_X)` of the shape `(𝓘^n 𝓕^•)`, for a bounded complex `𝓕^•` of
coherent `𝒪_X`-modules and a quasi-coherent ideal sheaf `𝓘` cutting out `X ∖ U`; its transition
maps are isomorphisms after restriction to `U`, so `(K_n|_U)` is a constant system, whose value is
the *value* of the Deligne system. Stacks 0G4L provides a Deligne system with any prescribed
value, unique as a pro-object, and Stacks 0G2H identifies `colim_n Hom_X(K_n, L)` with
`Hom_U(K, L|_U)` for a Deligne system with value `K`.

For a functor `j^* : 𝒟 ⥤ 𝒞` between pre-triangulated categories, an inverse system of
distinguished triangles `K_n ⟶ L_n ⟶ M_n ⟶ K_n[1]` of `𝒟` whose outer two systems are
pro-isomorphic to Deligne systems has middle system pro-isomorphic to a Deligne system. The
Deligne systems are given as the data of a `CategoryTheory.DeligneSystemValues`: an assignment of
an inverse system to each object of `𝒞` whose restriction along `j^*` is the constant system at
that object and which satisfies Stacks 0G2H.

## Main definitions

* `CategoryTheory.RestrictionLifting`: `colim_n Hom_𝒟(F_n, N) = colim_n Hom_𝒞(j^* F_n, j^* N)`,
  elementwise.
* `CategoryTheory.DeligneSystemValues`: an assignment of an inverse system to each object of `𝒞`,
  restricting to the constant system at that object and satisfying Stacks 0G2H.
* `CategoryTheory.DeligneSystemValues.ProIsoDeligne`: being pro-isomorphic to a Deligne system.

## Main results

* `CategoryTheory.DeligneSystemValues.proIsoDeligne_π₂`: in an inverse system of distinguished
  triangles whose outer systems are pro-isomorphic to Deligne systems, so is the middle system.
* `CategoryTheory.restrictionLifting_triangle`: `CategoryTheory.RestrictionLifting` for the outer
  systems of an inverse system of distinguished triangles gives it for the middle system.
* `CategoryTheory.proHomComparisonIso`: for an essentially constant restriction, the functor of
  points of the pro-object of `F` is `N ↦ Hom_𝒞(L, j^* N)`, where `L` is the value.
* `CategoryTheory.DeligneSystemValues.toAssignment`: the data above contains a
  `CategoryTheory.DeligneSystemAssignment`.

## References

* [Stacks Project, Tag 0G4Q](https://stacks.math.columbia.edu/tag/0G4Q)
* [Stacks Project, Tag 0G2H](https://stacks.math.columbia.edu/tag/0G2H)
* [Stacks Project, Tag 0G4L](https://stacks.math.columbia.edu/tag/0G4L)
* [Stacks Project, Tag 0G3A](https://stacks.math.columbia.edu/tag/0G3A)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Opposite

attribute [local instance] CategoryTheory.uliftCategory

universe v u u'

namespace CategoryTheory

section Lifting

variable {𝒟 : Type u} [Category.{v} 𝒟] {𝒞 : Type u'} [Category.{v} 𝒞]

/-- The direct system `n ↦ Mor(F_n, N)` of morphisms from an inverse sequence into a fixed
object. -/
public def homColimitDiagram (F : ℕᵒᵖ ⥤ 𝒟) (N : 𝒟) : ℕ ⥤ Type v where
  obj n := F.obj (op n) ⟶ N
  map := fun {X Y} (f : X ⟶ Y) => ↾fun (g : F.obj (op X) ⟶ N) => F.map f.op ≫ g
  map_id := by intro n; ext g; simp
  map_comp := by intro i j k f g; ext x; simp [Category.assoc]

/-- The cocone on `n ↦ Mor(F_n, N)` with vertex `Mor(A, R N)` attached to an identification of
`F ⋙ R` with the constant system at `A`: a morphism `f : F_n ⟶ N` is sent to the restriction
`R f` precomposed with the `n`-th component of that identification. -/
public def restrictionHomCocone (F : ℕᵒᵖ ⥤ 𝒟) (R : 𝒟 ⥤ 𝒞) (N : 𝒟) (A : 𝒞)
    (e : F ⋙ R ≅ (Functor.const ℕᵒᵖ).obj A) : Cocone (homColimitDiagram F N) where
  pt := A ⟶ R.obj N
  ι :=
    { app := fun n => ↾fun f => e.inv.app (op n) ≫ R.map f
      naturality := by
        intro n m f
        ext g
        change F.obj (op n) ⟶ N at g
        change e.inv.app (op m) ≫ R.map (F.map f.op ≫ g) = e.inv.app (op n) ≫ R.map g
        have h := e.inv.naturality f.op
        simpa [R.map_comp, Category.assoc] using congrArg (fun z => z ≫ R.map g) h.symm }

/-- `R` identifies `colim_n Mor(F_n, N)` with `colim_n Mor(R F_n, R N)`, elementwise: every
morphism `R F_n ⟶ R N` is, past some index, the restriction of a morphism `F_m ⟶ N`, and two
morphisms `F_n ⟶ N` with the same restriction agree past some index. -/
public structure RestrictionLifting (F : ℕᵒᵖ ⥤ 𝒟) (R : 𝒟 ⥤ 𝒞) (N : 𝒟) : Prop where
  /-- Every morphism out of a restricted term lifts, past some index. -/
  lift : ∀ (n : ℕ) (g : R.obj (F.obj (op n)) ⟶ R.obj N),
    ∃ (m : ℕ) (h : n ≤ m) (f : F.obj (op m) ⟶ N), R.map f = R.map (InverseSequence.tr F h) ≫ g
  /-- Two morphisms with equal restrictions agree past some index. -/
  eq : ∀ (n : ℕ) (f g : F.obj (op n) ⟶ N), R.map f = R.map g →
    ∃ (m : ℕ) (h : n ≤ m), InverseSequence.tr F h ≫ f = InverseSequence.tr F h ≫ g

/-- If the cocone `CategoryTheory.restrictionHomCocone` is a colimit cocone, then `R` identifies
the two colimits of `Hom`-sets elementwise, in the form `CategoryTheory.RestrictionLifting`. -/
public lemma restrictionLifting_of_isColimit (F : ℕᵒᵖ ⥤ 𝒟) (R : 𝒟 ⥤ 𝒞) (N : 𝒟) (A : 𝒞)
    (e : F ⋙ R ≅ (Functor.const ℕᵒᵖ).obj A)
    (hc : IsColimit (restrictionHomCocone F R N A e)) : RestrictionLifting F R N := by
  constructor
  · intro n g
    obtain ⟨m, f, hf⟩ := Types.jointly_surjective_of_isColimit hc (e.inv.app (op n) ≫ g)
    change F.obj (op m) ⟶ N at f
    change e.inv.app (op m) ≫ R.map f = e.inv.app (op n) ≫ g at hf
    have hn : n ≤ max n m := le_max_left _ _
    have hm : m ≤ max n m := le_max_right _ _
    refine ⟨max n m, hn, InverseSequence.tr F hm ≫ f, ?_⟩
    apply (cancel_epi (e.inv.app (op (max n m)))).mp
    rw [R.map_comp, ← Category.assoc, ← Category.assoc]
    have key {k : ℕ} (hk : k ≤ max n m) :
        e.inv.app (op (max n m)) ≫ R.map (InverseSequence.tr F hk) = e.inv.app (op k) := by
      simpa [InverseSequence.tr] using (e.inv.naturality (homOfLE hk).op).symm
    rwa [key hm, key hn]
  · intro n f g hfg
    have he : (restrictionHomCocone F R N A e).ι.app n f =
        (restrictionHomCocone F R N A e).ι.app n g := by
      show e.inv.app (op n) ≫ R.map f = e.inv.app (op n) ≫ R.map g
      rw [hfg]
    obtain ⟨m, a, b, hab⟩ := (Types.FilteredColimit.isColimit_eq_iff _ hc).mp he
    exact ⟨m, leOfHom a, hab⟩

/-- `CategoryTheory.RestrictionLifting` is invariant under pro-isomorphism of the inverse
sequence. -/
public lemma RestrictionLifting.of_proIso {F G : ℕᵒᵖ ⥤ 𝒟} (e : InverseSequence.ProIso F G)
    (R : 𝒟 ⥤ 𝒞) (N : 𝒟)
    (hG : RestrictionLifting G R N) : RestrictionLifting F R N := by
  have key {n m : ℕ} (hm : e.β n ≤ m) : e.φ m ≫ InverseSequence.tr G hm ≫ e.ψ n =
      InverseSequence.tr F ((e.βle n).trans (hm.trans (e.αle m))) := by
    rw [← Category.assoc, ← e.φnat hm, Category.assoc, e.ψφ n, tr_comp]
  constructor
  · intro n g
    obtain ⟨m, hm, f, hf⟩ := hG.lift (e.β n) (R.map (e.ψ n) ≫ g)
    refine ⟨e.α m, (e.βle n).trans (hm.trans (e.αle m)), e.φ m ≫ f, ?_⟩
    rw [R.map_comp, hf]
    simpa only [R.map_comp, Category.assoc] using congrArg (fun z => R.map z ≫ g) (key hm)
  · intro n f g hfg
    obtain ⟨m, hm, he⟩ := hG.eq (e.β n) (e.ψ n ≫ f) (e.ψ n ≫ g) (by simp only [R.map_comp, hfg])
    refine ⟨e.α m, (e.βle n).trans (hm.trans (e.αle m)), ?_⟩
    rw [← key hm]
    simpa only [Category.assoc] using congrArg (e.φ m ≫ ·) he

/-- `CategoryTheory.RestrictionLifting` is invariant under isomorphism of the inverse
sequence. -/
public lemma RestrictionLifting.of_natIso {F G : ℕᵒᵖ ⥤ 𝒟} (e : F ≅ G) (R : 𝒟 ⥤ 𝒞) (N : 𝒟)
    (hG : RestrictionLifting G R N) : RestrictionLifting F R N :=
  hG.of_proIso (Pro.proIsoOfNatIso e) R N

/-- `CategoryTheory.RestrictionLifting` transports along a fully faithful functor commuting with
the restriction. -/
public lemma RestrictionLifting.map_source {𝒟' : Type u} [Category.{v} 𝒟']
    {𝒞' : Type u'} [Category.{v} 𝒞'] {F : ℕᵒᵖ ⥤ 𝒟} {R : 𝒟 ⥤ 𝒞} {N : 𝒟}
    (hF : RestrictionLifting F R N) (S : 𝒟 ⥤ 𝒟') (S' : 𝒞 ⥤ 𝒞') [S.Full] [S.Faithful] [S'.Full]
    [S'.Faithful] (R' : 𝒟' ⥤ 𝒞') (e : S ⋙ R' ≅ R ⋙ S') {N' : 𝒟'} (t : S.obj N ≅ N') :
    RestrictionLifting (F ⋙ S) R' N' := by
  have commute {X Y : 𝒟} (f : X ⟶ Y) :
      R'.map (S.map f) = e.hom.app X ≫ S'.map (R.map f) ≫ e.inv.app Y := by
    have h := e.hom.naturality f
    simpa using congrArg (fun z => z ≫ e.inv.app Y) h
  constructor
  · intro n g
    let g' := S'.preimage (e.inv.app _ ≫ g ≫ R'.map t.inv ≫ e.hom.app N)
    obtain ⟨m, hm, f, hf⟩ := hF.lift n g'
    refine ⟨m, hm, S.map f ≫ t.hom, ?_⟩
    show R'.map (S.map f ≫ t.hom) = R'.map (S.map (InverseSequence.tr F hm)) ≫ g
    rw [R'.map_comp, commute f, hf, S'.map_comp, commute (InverseSequence.tr F hm)]
    dsimp only [g']
    rw [S'.map_preimage]
    simp only [Category.assoc, Iso.hom_inv_id_app_assoc, ← R'.map_comp, t.inv_hom_id, R'.map_id,
      Category.comp_id]
  · intro n f g hfg
    let f' := S.preimage (f ≫ t.inv)
    let g' := S.preimage (g ≫ t.inv)
    have hf : S.map f' = f ≫ t.inv := S.map_preimage _
    have hg : S.map g' = g ≫ t.inv := S.map_preimage _
    have hr : R.map f' = R.map g' := by
      apply S'.map_injective
      apply (cancel_epi (e.hom.app _)).mp
      apply (cancel_mono (e.inv.app N)).mp
      have hh : R'.map (S.map f') = R'.map (S.map g') := by
        rw [hf, hg, R'.map_comp, R'.map_comp, hfg]
      simpa only [commute, Category.assoc] using hh
    obtain ⟨m, hm, he⟩ := hF.eq n f' g' hr
    refine ⟨m, hm, ?_⟩
    have h := congrArg (fun z => S.map z ≫ t.hom) he
    show S.map (InverseSequence.tr F hm) ≫ f = S.map (InverseSequence.tr F hm) ≫ g
    simpa only [S.map_comp, Category.assoc, hf, hg, Iso.inv_hom_id, Category.comp_id] using h

/-- A morphism out of a term whose restriction vanishes vanishes past some index. -/
private lemma RestrictionLifting.exists_tr_comp_eq_zero [Preadditive 𝒟] [Preadditive 𝒞]
    {F : ℕᵒᵖ ⥤ 𝒟} {R : 𝒟 ⥤ 𝒞} [R.Additive] {N : 𝒟} (hF : RestrictionLifting F R N) (n : ℕ)
    (f : F.obj (op n) ⟶ N) (hf : R.map f = 0) :
    ∃ (m : ℕ) (h : n ≤ m), InverseSequence.tr F h ≫ f = 0 := by
  obtain ⟨m, h, he⟩ := hF.eq n f 0 (by rw [hf, R.map_zero])
  exact ⟨m, h, by simpa using he⟩

end Lifting

section Triangles

variable {𝒟 : Type u} [Category.{v} 𝒟] [Preadditive 𝒟] [HasZeroObject 𝒟] [HasShift 𝒟 ℤ]
  [∀ n : ℤ, (shiftFunctor 𝒟 n).Additive] [Pretriangulated 𝒟]
  {𝒞 : Type u'} [Category.{v} 𝒞] [Preadditive 𝒞] [HasZeroObject 𝒞] [HasShift 𝒞 ℤ]
  [∀ n : ℤ, (shiftFunctor 𝒞 n).Additive] [Pretriangulated 𝒞]

/-- Exactness of `Hom(-, N)` on a distinguished triangle at the first term: a morphism out of
`T.obj₁` whose shift kills `T.mor₃` factors through `T.mor₁`. -/
public lemma yoneda_exact₁_of_distTriang {T : Triangle 𝒟} (hT : T ∈ distTriang 𝒟) {N : 𝒟}
    (f : T.obj₁ ⟶ N) (hf : T.mor₃ ≫ f⟦(1 : ℤ)⟧' = 0) : ∃ g : T.obj₂ ⟶ N, f = T.mor₁ ≫ g := by
  obtain ⟨g, hg⟩ := Triangle.yoneda_exact₃ _ (rot_of_distTriang T hT) (f⟦(1 : ℤ)⟧') hf
  obtain ⟨g₀, hg₀⟩ : ∃ g₀ : T.obj₂⟦(1 : ℤ)⟧ ⟶ N⟦(1 : ℤ)⟧,
      (shiftFunctor 𝒟 (1 : ℤ)).map f = -((shiftFunctor 𝒟 (1 : ℤ)).map T.mor₁ ≫ g₀) :=
    ⟨g, hg.trans (Preadditive.neg_comp _ g)⟩
  obtain ⟨g', hg'⟩ : ∃ g' : T.obj₂ ⟶ N, (shiftFunctor 𝒟 (1 : ℤ)).map g' = -g₀ :=
    ⟨(shiftFunctor 𝒟 (1 : ℤ)).preimage (-g₀), (shiftFunctor 𝒟 (1 : ℤ)).map_preimage _⟩
  refine ⟨g', (shiftFunctor 𝒟 (1 : ℤ)).map_injective ?_⟩
  rw [(shiftFunctor 𝒟 (1 : ℤ)).map_comp, hg', Preadditive.comp_neg]
  exact hg₀

/-- The surjectivity half of the five lemma: in an inverse system of distinguished triangles whose
outer systems satisfy `CategoryTheory.RestrictionLifting`, every morphism out of a restricted
middle term lifts. -/
public lemma restrictionLifting_triangle_surj (R : 𝒟 ⥤ 𝒞) [R.Additive] [R.CommShift ℤ]
    [R.IsTriangulated] (T : ℕᵒᵖ ⥤ Triangle 𝒟) (hT : ∀ n, T.obj n ∈ distTriang 𝒟) (N : 𝒟)
    (hK : RestrictionLifting (T ⋙ Triangle.π₁) R N)
    (hM : RestrictionLifting (T ⋙ Triangle.π₃) R N)
    (hMp : RestrictionLifting (T ⋙ Triangle.π₃) R (N⟦(1 : ℤ)⟧))
    (n : ℕ) (g : R.obj ((T.obj (op n)).obj₂) ⟶ R.obj N) :
    ∃ (m : ℕ) (h : n ≤ m) (f : (T.obj (op m)).obj₂ ⟶ N),
      R.map f = R.map ((InverseSequence.tr T h).hom₂) ≫ g := by
  obtain ⟨m, hnm, a, ha⟩ := hK.lift n (R.map (T.obj (op n)).mor₁ ≫ g)
  change (T.obj (op m)).obj₁ ⟶ N at a
  change R.map a = R.map ((InverseSequence.tr T hnm).hom₁) ≫ R.map (T.obj (op n)).mor₁ ≫ g at ha
  let δ := (T.obj (op m)).mor₃ ≫ a⟦(1 : ℤ)⟧'
  have hδ : R.map δ = 0 := by
    apply (cancel_mono ((R.commShiftIso (1 : ℤ)).hom.app N)).mp
    have hnat := (R.commShiftIso (1 : ℤ)).hom.naturality a
    change R.map (a⟦(1 : ℤ)⟧') ≫ (R.commShiftIso (1 : ℤ)).hom.app N =
      (R.commShiftIso (1 : ℤ)).hom.app _ ≫ (R.map a)⟦(1 : ℤ)⟧' at hnat
    dsimp only [δ]
    rw [R.map_comp, Category.assoc, hnat, zero_comp, ← Category.assoc]
    show (R.map (T.obj (op m)).mor₃ ≫
      (R.commShiftIso (1 : ℤ)).hom.app (T.obj (op m)).obj₁) ≫ (R.map a)⟦(1 : ℤ)⟧' = 0
    rw [ha, Functor.map_comp, Functor.map_comp]
    have hcomm := (R.mapTriangle.map (InverseSequence.tr T hnm)).comm₃
    change (R.map (T.obj (op m)).mor₃ ≫
      (R.commShiftIso (1 : ℤ)).hom.app (T.obj (op m)).obj₁) ≫
        (R.map ((InverseSequence.tr T hnm).hom₁))⟦(1 : ℤ)⟧' =
      R.map ((InverseSequence.tr T hnm).hom₃) ≫ (R.map (T.obj (op n)).mor₃ ≫
        (R.commShiftIso (1 : ℤ)).hom.app (T.obj (op n)).obj₁) at hcomm
    have hz := comp_distTriang_mor_zero₃₁ _ (R.map_distinguished _ (hT (op n)))
    change (R.map (T.obj (op n)).mor₃ ≫
      (R.commShiftIso (1 : ℤ)).hom.app (T.obj (op n)).obj₁) ≫
        (R.map (T.obj (op n)).mor₁)⟦(1 : ℤ)⟧' = 0 at hz
    rw [← Category.assoc, ← Category.assoc, hcomm]
    simpa only [Category.assoc, comp_zero, zero_comp] using
      congrArg (fun z => R.map ((InverseSequence.tr T hnm).hom₃) ≫ z ≫ g⟦(1 : ℤ)⟧') hz
  obtain ⟨k, hmk, hk⟩ := hMp.exists_tr_comp_eq_zero m δ hδ
  change (InverseSequence.tr T hmk).hom₃ ≫ δ = 0 at hk
  have hk' : (T.obj (op k)).mor₃ ≫ ((InverseSequence.tr T hmk).hom₁ ≫ a)⟦(1 : ℤ)⟧' = 0 := by
    rw [Functor.map_comp, ← Category.assoc, (InverseSequence.tr T hmk).comm₃, Category.assoc]
    simpa [δ] using hk
  obtain ⟨b, hb⟩ :=
    yoneda_exact₁_of_distTriang (hT (op k)) ((InverseSequence.tr T hmk).hom₁ ≫ a) hk'
  let hnk := hnm.trans hmk
  let d := R.map ((InverseSequence.tr T hnk).hom₂) ≫ g - R.map b
  have hd : (R.mapTriangle.obj (T.obj (op k))).mor₁ ≫ d = 0 := by
    show R.map (T.obj (op k)).mor₁ ≫ (R.map ((InverseSequence.tr T hnk).hom₂) ≫ g - R.map b) = 0
    rw [Preadditive.comp_sub, sub_eq_zero]
    calc
      _ = R.map ((InverseSequence.tr T hnk).hom₁) ≫ R.map (T.obj (op n)).mor₁ ≫ g := by
        rw [← Category.assoc, ← R.map_comp, (InverseSequence.tr T hnk).comm₁, R.map_comp,
          Category.assoc]
      _ = R.map ((InverseSequence.tr T hmk).hom₁) ≫ R.map a := by
        rw [← tr_comp T hmk hnm, comp_hom₁, R.map_comp, Category.assoc, ha]
      _ = _ := by rw [← R.map_comp, hb, R.map_comp]
  obtain ⟨c, hc⟩ := Triangle.yoneda_exact₂ _ (R.map_distinguished _ (hT (op k))) d hd
  change R.obj (T.obj (op k)).obj₃ ⟶ R.obj N at c
  change d = R.map (T.obj (op k)).mor₂ ≫ c at hc
  obtain ⟨p, hkp, c', hc'⟩ := hM.lift k c
  change (T.obj (op p)).obj₃ ⟶ N at c'
  change R.map c' = R.map ((InverseSequence.tr T hkp).hom₃) ≫ c at hc'
  refine ⟨p, hnk.trans hkp, (InverseSequence.tr T hkp).hom₂ ≫ b + (T.obj (op p)).mor₂ ≫ c', ?_⟩
  rw [R.map_add, R.map_comp, R.map_comp, hc', ← Category.assoc,
    ← R.map_comp (T.obj (op p)).mor₂ ((InverseSequence.tr T hkp).hom₃),
    (InverseSequence.tr T hkp).comm₂, R.map_comp,
    Category.assoc]
  rw [← hc, ← Preadditive.comp_add]
  dsimp only [d]
  rw [add_sub_cancel, ← Category.assoc, ← R.map_comp]
  congr 2
  exact congrArg TriangleMorphism.hom₂ (tr_comp T hkp hnk)

/-- The injectivity half of the five lemma: in an inverse system of distinguished triangles whose
outer systems satisfy `CategoryTheory.RestrictionLifting`, a morphism out of a middle term with
vanishing restriction vanishes past some index. -/
public lemma restrictionLifting_triangle_zero (R : 𝒟 ⥤ 𝒞) [R.Additive] [R.CommShift ℤ]
    [R.IsTriangulated] (T : ℕᵒᵖ ⥤ Triangle 𝒟) (hT : ∀ n, T.obj n ∈ distTriang 𝒟) (N : 𝒟)
    (hK : RestrictionLifting (T ⋙ Triangle.π₁) R N)
    (hM : RestrictionLifting (T ⋙ Triangle.π₃) R N)
    (hKp : RestrictionLifting ((T ⋙ Triangle.π₁) ⋙ shiftFunctor 𝒟 (1 : ℤ)) R N)
    (n : ℕ) (f : (T.obj (op n)).obj₂ ⟶ N) (hf : R.map f = 0) :
    ∃ (m : ℕ) (h : n ≤ m), (InverseSequence.tr T h).hom₂ ≫ f = 0 := by
  have hz : R.map ((T.obj (op n)).mor₁ ≫ f) = 0 := by rw [R.map_comp, hf, comp_zero]
  obtain ⟨m, hnm, hm⟩ := hK.exists_tr_comp_eq_zero n ((T.obj (op n)).mor₁ ≫ f) hz
  change (InverseSequence.tr T hnm).hom₁ ≫ ((T.obj (op n)).mor₁ ≫ f) = 0 at hm
  have hb : (T.obj (op m)).mor₁ ≫ ((InverseSequence.tr T hnm).hom₂ ≫ f) = 0 := by
    rw [← Category.assoc, (InverseSequence.tr T hnm).comm₁, Category.assoc]
    simpa using hm
  obtain ⟨c, hc⟩ := Triangle.yoneda_exact₂ _ (hT (op m)) ((InverseSequence.tr T hnm).hom₂ ≫ f) hb
  have hcR : (R.mapTriangle.obj (T.obj (op m))).mor₂ ≫ R.map c = 0 := by
    show R.map (T.obj (op m)).mor₂ ≫ R.map c = 0
    rw [← R.map_comp, ← hc, R.map_comp, hf, comp_zero]
  obtain ⟨a, ha⟩ := Triangle.yoneda_exact₃ _ (R.map_distinguished _ (hT (op m))) (R.map c) hcR
  change (R.obj (T.obj (op m)).obj₁)⟦(1 : ℤ)⟧ ⟶ R.obj N at a
  change R.map c = (R.map (T.obj (op m)).mor₃ ≫
    (R.commShiftIso (1 : ℤ)).hom.app (T.obj (op m)).obj₁) ≫ a at ha
  obtain ⟨p, hmp, a', ha'⟩ := hKp.lift m
    ((R.commShiftIso (1 : ℤ)).hom.app (T.obj (op m)).obj₁ ≫ a)
  change ((T.obj (op p)).obj₁⟦(1 : ℤ)⟧) ⟶ N at a'
  change R.map a' = R.map ((InverseSequence.tr T hmp).hom₁⟦(1 : ℤ)⟧') ≫
    (R.commShiftIso (1 : ℤ)).hom.app (T.obj (op m)).obj₁ ≫ a at ha'
  let δ := (InverseSequence.tr T hmp).hom₃ ≫ c - (T.obj (op p)).mor₃ ≫ a'
  have hδ : R.map δ = 0 := by
    dsimp only [δ]
    rw [R.map_sub, sub_eq_zero, R.map_comp, R.map_comp, ha', ← Category.assoc,
      ← R.map_comp (T.obj (op p)).mor₃ ((InverseSequence.tr T hmp).hom₁⟦(1 : ℤ)⟧'),
      (InverseSequence.tr T hmp).comm₃, R.map_comp]
    simpa only [Category.assoc] using
      congrArg (fun z => R.map ((InverseSequence.tr T hmp).hom₃) ≫ z) ha
  obtain ⟨q, hpq, hq⟩ := hM.exists_tr_comp_eq_zero p δ hδ
  change (InverseSequence.tr T hpq).hom₃ ≫ δ = 0 at hq
  have hq' : (InverseSequence.tr T hpq).hom₃ ≫ (InverseSequence.tr T hmp).hom₃ ≫ c =
      (InverseSequence.tr T hpq).hom₃ ≫ (T.obj (op p)).mor₃ ≫ a' := by
    simpa only [δ, Preadditive.comp_sub, sub_eq_zero] using hq
  refine ⟨q, hnm.trans (hmp.trans hpq), ?_⟩
  have ht : (InverseSequence.tr T (hnm.trans (hmp.trans hpq))).hom₂ =
      (InverseSequence.tr T hpq).hom₂ ≫ (InverseSequence.tr T hmp).hom₂ ≫
        (InverseSequence.tr T hnm).hom₂ := by
    rw [← comp_hom₂, ← comp_hom₂, tr_comp, tr_comp]
  rw [ht, Category.assoc, Category.assoc, hc, ← (InverseSequence.tr T hmp).comm₂_assoc,
    ← (InverseSequence.tr T hpq).comm₂_assoc, hq', (InverseSequence.tr T hpq).comm₂_assoc,
    ← Category.assoc (T.obj (op p)).mor₂,
    comp_distTriang_mor_zero₂₃ _ (hT (op p)), zero_comp, comp_zero]

/-- **The five lemma for the colimits of `Hom`-groups.** In an inverse system of distinguished
triangles, `CategoryTheory.RestrictionLifting` for the outer two systems — in the four instances
the long exact sequences use — gives it for the middle system. -/
public lemma restrictionLifting_triangle (R : 𝒟 ⥤ 𝒞) [R.Additive] [R.CommShift ℤ]
    [R.IsTriangulated] (T : ℕᵒᵖ ⥤ Triangle 𝒟) (hT : ∀ n, T.obj n ∈ distTriang 𝒟) (N : 𝒟)
    (hK : RestrictionLifting (T ⋙ Triangle.π₁) R N)
    (hM : RestrictionLifting (T ⋙ Triangle.π₃) R N)
    (hMp : RestrictionLifting (T ⋙ Triangle.π₃) R (N⟦(1 : ℤ)⟧))
    (hKp : RestrictionLifting ((T ⋙ Triangle.π₁) ⋙ shiftFunctor 𝒟 (1 : ℤ)) R N) :
    RestrictionLifting (T ⋙ Triangle.π₂) R N := by
  constructor
  · exact restrictionLifting_triangle_surj R T hT N hK hM hMp
  · intro n f g hfg
    change (T.obj (op n)).obj₂ ⟶ N at f g
    change R.map f = R.map g at hfg
    obtain ⟨m, h, he⟩ := restrictionLifting_triangle_zero R T hT N hK hM hKp n (f - g)
      (by rw [R.map_sub, hfg, sub_self])
    refine ⟨m, h, ?_⟩
    show (InverseSequence.tr T h).hom₂ ≫ f = (InverseSequence.tr T h).hom₂ ≫ g
    simpa only [Preadditive.comp_sub, sub_eq_zero] using he

end Triangles

section Comparison

variable {𝒟 : Type u} [Category.{v} 𝒟] {𝒞 : Type u'} [Category.{v} 𝒞]

/-- The comparison `colim_n Mor(F_n, N) ⟶ Mor(c.pt, R N)` attached to a cone `c` on `F ⋙ R`: the
class of `f : F_n ⟶ N` is sent to the `n`-th leg of `c` followed by `R f`. -/
public def proHomComparison (F : ℕᵒᵖ ⥤ 𝒟) (R : 𝒟 ⥤ 𝒞) (c : Cone (F ⋙ R)) :
    Pro.seqHomColim F ⟶ R ⋙ coyoneda.obj (op c.pt) :=
  colimit.desc (F.op ⋙ coyoneda)
    { pt := R ⋙ coyoneda.obj (op c.pt)
      ι :=
        { app := fun n =>
            { app := fun N => ↾fun f => c.π.app n.unop ≫ R.map f
              naturality := by
                intro N M g
                ext f
                change c.π.app n.unop ≫ R.map (f ≫ g) = (c.π.app n.unop ≫ R.map f) ≫ R.map g
                simp [R.map_comp, Category.assoc] }
          naturality := by
            intro n m a
            ext N f
            change c.π.app m.unop ≫ R.map (F.map a.unop ≫ f) = c.π.app n.unop ≫ R.map f
            rw [R.map_comp, ← Category.assoc]
            exact congrArg (fun z => z ≫ R.map f) (c.w a.unop) } }

/-- The comparison sends the class of `f : F_n ⟶ N` to `c.π.app n ≫ R f`. -/
public lemma proHomComparison_stage (F : ℕᵒᵖ ⥤ 𝒟) (R : 𝒟 ⥤ 𝒞) (c : Cone (F ⋙ R)) {N : 𝒟}
    {n : ℕ} (f : F.obj (op n) ⟶ N) :
    (proHomComparison F R c).app N (Pro.seqStage F f) = c.π.app (op n) ≫ R.map f := by
  show ((colimit.ι (F.op ⋙ coyoneda) (op (op n)) ≫ proHomComparison F R c).app N) f = _
  simp only [proHomComparison, colimit.ι_desc]
  rfl

/-- If the restricted system is essentially constant with value `c.pt` and `R` identifies the two
colimits of `Hom`-sets at `N`, then the comparison is bijective at `N`. -/
public lemma proHomComparison_bijective (F : ℕᵒᵖ ⥤ 𝒟) (R : 𝒟 ⥤ 𝒞) (c : Cone (F ⋙ R)) (i : ℕᵒᵖ)
    (s : R.obj (F.obj i) ⟶ c.pt)
    (hc : EssentiallyConstantPro.IsEssentiallyConstantWith (F ⋙ R) c i s) (N : 𝒟)
    (hF : RestrictionLifting F R N) : Function.Bijective ((proHomComparison F R c).app N) := by
  constructor
  · intro x y hxy
    obtain ⟨n, f, rfl⟩ := Pro.seqStage_surjective F N x
    obtain ⟨m, g, rfl⟩ := Pro.seqStage_surjective F N y
    rw [proHomComparison_stage, proHomComparison_stage] at hxy
    have hn : n ≤ max n m := le_max_left _ _
    have hm : m ≤ max n m := le_max_right _ _
    have hk : c.π.app (op (max n m)) ≫ R.map (InverseSequence.tr F hn ≫ f) =
        c.π.app (op (max n m)) ≫ R.map (InverseSequence.tr F hm ≫ g) := by
      have hn' : c.π.app (op (max n m)) ≫ R.map (InverseSequence.tr F hn) = c.π.app (op n) := c.w _
      have hm' : c.π.app (op (max n m)) ≫ R.map (InverseSequence.tr F hm) = c.π.app (op m) := c.w _
      simpa only [R.map_comp, ← Category.assoc, hn', hm'] using hxy
    obtain ⟨l, σ, τ, hl⟩ := hc.cofinal (op (max n m))
    have hkl : max n m ≤ l.unop := leOfHom τ.unop
    have hl' : R.map (InverseSequence.tr F hkl) = R.map (F.map σ) ≫ s ≫ c.π.app (op (max n m)) := hl
    have hk' : c.π.app (op (max n m)) ≫ R.map (InverseSequence.tr F hn) ≫ R.map f =
        c.π.app (op (max n m)) ≫ R.map (InverseSequence.tr F hm) ≫ R.map g := by
      simpa only [R.map_comp, Category.assoc] using hk
    have he : R.map (InverseSequence.tr F hkl ≫ (InverseSequence.tr F hn ≫ f)) =
        R.map (InverseSequence.tr F hkl ≫ (InverseSequence.tr F hm ≫ g)) := by
      simp only [R.map_comp, hl', Category.assoc]
      exact congrArg (fun z => R.map (F.map σ) ≫ s ≫ z) hk'
    obtain ⟨q, hq, heq⟩ := hF.eq l.unop (InverseSequence.tr F hkl ≫ (InverseSequence.tr F hn ≫ f))
      (InverseSequence.tr F hkl ≫ (InverseSequence.tr F hm ≫ g)) he
    have h := congrArg (Pro.seqStage F) heq
    simpa only [Pro.seqStage_transition] using h
  · intro g
    change c.pt ⟶ R.obj N at g
    obtain ⟨m, hm, f, hf⟩ := hF.lift i.unop (s ≫ g)
    refine ⟨Pro.seqStage F f, ?_⟩
    rw [proHomComparison_stage, hf, ← Category.assoc]
    have hi : c.π.app (op m) ≫ R.map (InverseSequence.tr F hm) = c.π.app i := c.w _
    rw [hi, ← Category.assoc, hc.retraction]
    exact Category.id_comp g

/-- **The functor of points of a pro-object with essentially constant restriction.** If the
restriction `F ⋙ R` is essentially constant with value `c.pt` and `R` identifies the colimits of
`Hom`-sets at every object, then `colim_n Mor(F_n, -) = Mor(c.pt, R -)`. -/
public def proHomComparisonIso (F : ℕᵒᵖ ⥤ 𝒟) (R : 𝒟 ⥤ 𝒞) (c : Cone (F ⋙ R)) (i : ℕᵒᵖ)
    (s : R.obj (F.obj i) ⟶ c.pt)
    (hc : EssentiallyConstantPro.IsEssentiallyConstantWith (F ⋙ R) c i s)
    (hF : ∀ N, RestrictionLifting F R N) : Pro.seqHomColim F ≅ R ⋙ coyoneda.obj (op c.pt) := by
  have h : ∀ N, IsIso ((proHomComparison F R c).app N) := fun N =>
    (isIso_iff_bijective _).mpr (proHomComparison_bijective F R c i s hc N (hF N))
  have : IsIso (proHomComparison F R c) := NatIso.isIso_of_isIso_app _
  exact asIso (proHomComparison F R c)

/-- A cone transported along an isomorphism of the diagrams. -/
public def coneOfNatIso {F G : ℕᵒᵖ ⥤ 𝒟} (e : F ≅ G) (c : Cone G) : Cone F where
  pt := c.pt
  π := c.π ≫ e.inv

/-- An essential-constancy witness transported along an isomorphism of the diagrams. -/
public lemma essentiallyConstantWith_of_natIso {F G : ℕᵒᵖ ⥤ 𝒟} (e : F ≅ G) (c : Cone G)
    (i : ℕᵒᵖ) (s : G.obj i ⟶ c.pt)
    (hc : EssentiallyConstantPro.IsEssentiallyConstantWith G c i s) :
    EssentiallyConstantPro.IsEssentiallyConstantWith F (coneOfNatIso e c) i
      (e.hom.app i ≫ s) := by
  constructor
  · simpa [coneOfNatIso] using hc.retraction
  · intro j
    obtain ⟨k, a, b, h⟩ := hc.cofinal j
    refine ⟨k, a, b, ?_⟩
    show F.map b = F.map a ≫ (e.hom.app i ≫ s) ≫ (c.π.app j ≫ e.inv.app j)
    calc
      F.map b = e.hom.app k ≫ G.map b ≫ e.inv.app j := by simp
      _ = e.hom.app k ≫ G.map a ≫ s ≫ c.π.app j ≫ e.inv.app j := by
        rw [h]; simp only [Category.assoc]
      _ = _ := by rw [← e.hom.naturality_assoc]; simp only [Category.assoc]

/-- A constant inverse sequence is essentially constant, with the identity as witness. -/
public lemma essentiallyConstantWith_const (A : 𝒟) :
    EssentiallyConstantPro.IsEssentiallyConstantWith ((Functor.const ℕᵒᵖ).obj A) ⟨A, 𝟙 _⟩ (op 0)
      (𝟙 A) := by
  constructor
  · simp
  · intro j
    exact ⟨j, (homOfLE (Nat.zero_le j.unop)).op, 𝟙 _, by simp⟩

end Comparison

section Deligne

variable {𝒟 : Type u} [Category.{v} 𝒟] {𝒞 : Type u'} [Category.{v} 𝒞]

/-- A **Deligne system assignment with values** for a functor `j^* : 𝒟 ⥤ 𝒞`: an inverse sequence
`system K` in `𝒟` for every object `K` of `𝒞`, whose restriction along `j^*` is the constant
system at `K`, and for which Stacks 0G2H holds, namely `colim_n Mor_𝒟(system K n, N)` is
`Mor_𝒞(K, j^* N)` through `CategoryTheory.restrictionHomCocone`. -/
public structure DeligneSystemValues (jstar : 𝒟 ⥤ 𝒞) where
  /-- The inverse sequence assigned to an object of `𝒞`. -/
  system : 𝒞 → (ℕᵒᵖ ⥤ 𝒟)
  /-- The assigned sequence restricts to the constant system at the given object: it is a Deligne
  system whose value is that object. -/
  restrictIso : ∀ K : 𝒞, system K ⋙ jstar ≅ (Functor.const ℕᵒᵖ).obj K
  /-- Stacks 0G2H: `colim_n Mor_𝒟(system K n, N) = Mor_𝒞(K, j^* N)`. -/
  isColimit : ∀ (K : 𝒞) (N : 𝒟),
    IsColimit (restrictionHomCocone (system K) jstar N K (restrictIso K))

namespace DeligneSystemValues

variable {jstar : 𝒟 ⥤ 𝒞} (A : DeligneSystemValues jstar)

/-- Stacks 0G2H for an assigned system, in the form `CategoryTheory.RestrictionLifting`. -/
public lemma restrictionLifting (K : 𝒞) (N : 𝒟) : RestrictionLifting (A.system K) jstar N :=
  restrictionLifting_of_isColimit _ _ _ _ (A.restrictIso K) (A.isColimit K N)

/-- The constant cone on the restriction of an assigned system, with vertex its value. -/
public def restrictCone (K : 𝒞) : Cone (A.system K ⋙ jstar) :=
  coneOfNatIso (A.restrictIso K) ⟨K, 𝟙 _⟩

/-- The restriction of an assigned system is essentially constant with value its value. -/
public lemma isEssentiallyConstantWith_restrict (K : 𝒞) :
    EssentiallyConstantPro.IsEssentiallyConstantWith (A.system K ⋙ jstar) (A.restrictCone K)
      (op 0) ((A.restrictIso K).hom.app (op 0) ≫ 𝟙 K) :=
  essentiallyConstantWith_of_natIso (A.restrictIso K) ⟨K, 𝟙 _⟩ (op 0) (𝟙 K)
    (essentiallyConstantWith_const K)

/-- The functor of points of the pro-object of an assigned system is `N ↦ Mor_𝒞(K, j^* N)`. -/
public def systemHomIso (K : 𝒞) :
    Pro.seqHomColim (A.system K) ≅ jstar ⋙ coyoneda.obj (op K) :=
  proHomComparisonIso (A.system K) jstar (A.restrictCone K) (op 0)
    ((A.restrictIso K).hom.app (op 0) ≫ 𝟙 K) (A.isEssentiallyConstantWith_restrict K)
    (A.restrictionLifting K)

/-- A Deligne system assignment with values is in particular a
`CategoryTheory.DeligneSystemAssignment`. -/
public def toAssignment : DeligneSystemAssignment jstar where
  system := A.system
  homIso := fun K => (A.systemHomIso K).symm ≪≫ (Pro.seqHomColimIso (A.system K)).symm

/-- An inverse sequence in `𝒟` is **pro-isomorphic to a Deligne system** when it is isomorphic,
as a pro-object, to one of the assigned systems. -/
public def ProIsoDeligne (F : ℕᵒᵖ ⥤ 𝒟) : Prop :=
  ∃ K : 𝒞, Nonempty (ProSeq.of F ≅ ProSeq.of (A.system K))

/-- A sequence pro-isomorphic to a Deligne system satisfies Stacks 0G2H in the form
`CategoryTheory.RestrictionLifting`. -/
public lemma restrictionLifting_of_proIsoDeligne {F : ℕᵒᵖ ⥤ 𝒟} (hF : A.ProIsoDeligne F) (N : 𝒟) :
    RestrictionLifting F jstar N := by
  obtain ⟨K, ⟨i⟩⟩ := hF
  exact (A.restrictionLifting K N).of_proIso (ProSeq.proIsoOfIso i) jstar N

/-- The restriction of a sequence pro-isomorphic to a Deligne system is an essentially constant
pro-object. -/
public lemma isEssentiallyConstantPro_of_proIsoDeligne {F : ℕᵒᵖ ⥤ 𝒟} (hF : A.ProIsoDeligne F) :
    EssentiallyConstantPro.IsEssentiallyConstantPro (F ⋙ jstar) := by
  obtain ⟨K, ⟨i⟩⟩ := hF
  exact Pro.isEssentiallyConstantPro_of_proIso_const
    (Pro.proIsoTrans (Pro.proIsoWhiskerRight (ProSeq.proIsoOfIso i) jstar)
      (Pro.proIsoOfNatIso (A.restrictIso K)))

end DeligneSystemValues

end Deligne

section Main

variable {𝒟 : Type u} [Category.{v} 𝒟] [Preadditive 𝒟] [HasZeroObject 𝒟] [HasShift 𝒟 ℤ]
  [∀ n : ℤ, (shiftFunctor 𝒟 n).Additive] [Pretriangulated 𝒟]
  {𝒞 : Type u'} [Category.{v} 𝒞] [Preadditive 𝒞] [HasZeroObject 𝒞] [HasShift 𝒞 ℤ]
  [∀ n : ℤ, (shiftFunctor 𝒞 n).Additive] [Pretriangulated 𝒞]

/-- Let `j^* : 𝒟 ⥤ 𝒞` be a triangulated functor with a Deligne system assignment, and let
`K_n ⟶ L_n ⟶ M_n ⟶ K_n[1]` be an inverse system of distinguished triangles in `𝒟`. If `(K_n)`
and `(M_n)` are pro-isomorphic to Deligne systems, then so is `(L_n)`. -/
@[stacks 0G4Q "for a Deligne-system assignment supplied as data, including the colimit \
identification of Stacks 0G2H as its isColimit field"]
public theorem DeligneSystemValues.proIsoDeligne_π₂ {jstar : 𝒟 ⥤ 𝒞} [jstar.Additive]
    [jstar.CommShift ℤ] [jstar.IsTriangulated] (A : DeligneSystemValues jstar)
    (T : ℕᵒᵖ ⥤ Triangle 𝒟) (hT : ∀ n, T.obj n ∈ distTriang 𝒟)
    (hK : A.ProIsoDeligne (T ⋙ Triangle.π₁)) (hM : A.ProIsoDeligne (T ⋙ Triangle.π₃)) :
    A.ProIsoDeligne (T ⋙ Triangle.π₂) := by
  have hKlift : ∀ N, RestrictionLifting (T ⋙ Triangle.π₁) jstar N :=
    A.restrictionLifting_of_proIsoDeligne hK
  have hMlift : ∀ N, RestrictionLifting (T ⋙ Triangle.π₃) jstar N :=
    A.restrictionLifting_of_proIsoDeligne hM
  have hKplift : ∀ N, RestrictionLifting ((T ⋙ Triangle.π₁) ⋙ shiftFunctor 𝒟 (1 : ℤ)) jstar N :=
    fun N => (hKlift (N⟦(-1 : ℤ)⟧)).map_source (shiftFunctor 𝒟 (1 : ℤ))
      (shiftFunctor 𝒞 (1 : ℤ)) jstar (jstar.commShiftIso (1 : ℤ))
      ((shiftFunctorCompIsoId 𝒟 (-1 : ℤ) 1 (by decide)).app N)
  have hLlift : ∀ N, RestrictionLifting (T ⋙ Triangle.π₂) jstar N := fun N =>
    restrictionLifting_triangle jstar T hT N (hKlift N) (hMlift N) (hMlift (N⟦(1 : ℤ)⟧))
      (hKplift N)
  have hT' : ∀ n, (T ⋙ jstar.mapTriangle).obj n ∈ distTriang 𝒞 := fun n =>
    jstar.map_distinguished _ (hT n)
  have hecK : EssentiallyConstantInd.IsEssentiallyConstantInd
      (((T ⋙ jstar.mapTriangle) ⋙ Triangle.π₁).op) :=
    (EssentiallyConstantPro.isEssentiallyConstantPro_iff_op _).mp
      (A.isEssentiallyConstantPro_of_proIsoDeligne hK)
  have hecM : EssentiallyConstantInd.IsEssentiallyConstantInd
      (((T ⋙ jstar.mapTriangle) ⋙ Triangle.π₃).op) :=
    (EssentiallyConstantPro.isEssentiallyConstantPro_iff_op _).mp
      (A.isEssentiallyConstantPro_of_proIsoDeligne hM)
  obtain ⟨c, i, s, hs⟩ := (EssentiallyConstantPro.isEssentiallyConstantPro_iff_op
    ((T ⋙ Triangle.π₂) ⋙ jstar)).mpr
      (Pretriangulated.isEssentiallyConstant_op_π₂_and_exists_limit_triangle
        (T ⋙ jstar.mapTriangle) hT' hecK hecM).1
  exact ⟨c.pt, ⟨ProSeq.isoOfSeqHomColimIso
    (proHomComparisonIso (T ⋙ Triangle.π₂) jstar c i s hs hLlift ≪≫
      (A.systemHomIso c.pt).symm)⟩⟩

end Main

end CategoryTheory

end
