module

public import StacksFrontier.AlgebraicGeometry.Simplicial.CoveringGlueing.RestrictionCoherence

/-!
# Derived objects given on a covering, glued along the pairwise overlaps

Let `(C, O_C)` be a ringed site with fibre products and let `f_i : U_i ⟶ X` be a family of
arrows of `C`. Suppose given objects `E_i` of `D(O_{U_i})` and isomorphisms
`ρ_{ij} : E_i|_{U_{ij}} ⟶ E_j|_{U_{ij}}` over the fibre products `U_{ij} = U_i ×_X U_j`. For
arrows `a : W ⟶ U_i` and `b : W ⟶ U_j` agreeing over `X`, restricting `ρ_{ij}` along the induced
arrow `W ⟶ U_{ij}` gives an isomorphism `E_i|_W ⟶ E_j|_W`. The `ρ_{ij}` satisfy the *cocycle
condition* when on the triple fibre products `U_{ijk}` the composite of the restrictions of
`ρ_{ij}` and `ρ_{jk}` is the restriction of `ρ_{ik}`.

This file shows that the cocycle condition then holds at every object `W` carrying arrows into
`U_i`, `U_j`, `U_k` over `X`, and deduces that the isomorphism attached to a pair `(a, a)` is the
identity and that the isomorphisms attached to `(a, b)` and `(b, a)` are mutually inverse.

## Main definitions

* `AlgebraicGeometry.RingedSite.CoveringGlueing.overlapIso`: the isomorphism `E_i|_W ⟶ E_j|_W`
  attached to arrows `a : W ⟶ U_i` and `b : W ⟶ U_j` agreeing over `X`.
* `AlgebraicGeometry.RingedSite.CoveringGlueing.IsCocycle`: the cocycle condition on the triple
  fibre products `U_i ×_X U_j ×_X U_k`.

## Main results

* `AlgebraicGeometry.RingedSite.CoveringGlueing.overlapIso_restrict`: the isomorphism attached to
  `(h ≫ a, h ≫ b)` is the restriction along `h` of the isomorphism attached to `(a, b)`.
* `AlgebraicGeometry.RingedSite.CoveringGlueing.overlapIso_trans`: the cocycle condition at an
  arbitrary object.
* `AlgebraicGeometry.RingedSite.CoveringGlueing.overlapIso_self` and `.overlapIso_symm`.
* `AlgebraicGeometry.RingedSite.CoveringGlueing.overlapIso_fst_snd`: on `U_{ij}` itself the
  attached isomorphism is `ρ_{ij}`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.RingedSite.CoveringGlueing

attribute [local instance] HasDerivedCategory.standard

variable {X : RingedSite.{u, u, u}} [HasPullbacks X.C] {X₀ : X.C} {ι : Type*} {U : ι → X.C}
  (f : ∀ i, U i ⟶ X₀) {E : ∀ i, LocalDerivedCategory.{0} X (U i)}
  (ρ : ∀ i j, (derivedOverMap.{0} X (pullback.fst (f i) (f j))).obj (E i) ≅
    (derivedOverMap.{0} X (pullback.snd (f i) (f j))).obj (E j))

/-- The isomorphism `E_i|_W ⟶ E_j|_W` obtained from `ρ_{ij}` by restriction along the arrow
`W ⟶ U_{ij}` induced by arrows `a : W ⟶ U_i` and `b : W ⟶ U_j` agreeing over `X`. -/
def overlapIso {i j : ι} {W : X.C} (a : W ⟶ U i) (b : W ⟶ U j) (hab : a ≫ f i = b ≫ f j) :
    (derivedOverMap.{0} X a).obj (E i) ≅ (derivedOverMap.{0} X b).obj (E j) :=
  (derivedOverMapComp.{0} X (pullback.lift_fst a b hab)).app (E i) ≪≫
    (derivedOverMap.{0} X (pullback.lift a b hab)).mapIso (ρ i j) ≪≫
    ((derivedOverMapComp.{0} X (pullback.lift_snd a b hab)).app (E j)).symm

/-- The triple fibre product `U_{ijk} = U_i ×_X U_j ×_X U_k`, presented as `U_{ij} ×_X U_k`. -/
abbrev tripleOverlap (i j k : ι) : X.C :=
  pullback (pullback.fst (f i) (f j) ≫ f i) (f k)

/-- The projection `U_{ijk} ⟶ U_i`. -/
abbrev tripleFst (i j k : ι) : tripleOverlap f i j k ⟶ U i :=
  pullback.fst _ (f k) ≫ pullback.fst (f i) (f j)

/-- The projection `U_{ijk} ⟶ U_j`. -/
abbrev tripleSnd (i j k : ι) : tripleOverlap f i j k ⟶ U j :=
  pullback.fst _ (f k) ≫ pullback.snd (f i) (f j)

/-- The projection `U_{ijk} ⟶ U_k`. -/
abbrev tripleThd (i j k : ι) : tripleOverlap f i j k ⟶ U k :=
  pullback.snd _ (f k)

/-- The projections `U_{ijk} ⟶ U_i` and `U_{ijk} ⟶ U_j` agree over `X`. -/
theorem tripleFst_comp_eq_tripleSnd_comp (i j k : ι) :
    tripleFst f i j k ≫ f i = tripleSnd f i j k ≫ f j := by
  simp [Category.assoc, pullback.condition]

/-- The projections `U_{ijk} ⟶ U_i` and `U_{ijk} ⟶ U_k` agree over `X`. -/
theorem tripleFst_comp_eq_tripleThd_comp (i j k : ι) :
    tripleFst f i j k ≫ f i = tripleThd f i j k ≫ f k := by
  simpa [Category.assoc] using pullback.condition (f := pullback.fst (f i) (f j) ≫ f i)
    (g := f k)

/-- The projections `U_{ijk} ⟶ U_j` and `U_{ijk} ⟶ U_k` agree over `X`. -/
theorem tripleSnd_comp_eq_tripleThd_comp (i j k : ι) :
    tripleSnd f i j k ≫ f j = tripleThd f i j k ≫ f k := by
  rw [← tripleFst_comp_eq_tripleSnd_comp, tripleFst_comp_eq_tripleThd_comp]

/-- **The cocycle condition** for the `ρ_{ij}`: on every triple fibre product
`U_i ×_X U_j ×_X U_k`, the restriction of `ρ_{ij}` followed by that of `ρ_{jk}` is the
restriction of `ρ_{ik}`. -/
def IsCocycle : Prop :=
  ∀ i j k : ι,
    (overlapIso f ρ (tripleFst f i j k) (tripleSnd f i j k)
        (tripleFst_comp_eq_tripleSnd_comp f i j k)).hom ≫
      (overlapIso f ρ (tripleSnd f i j k) (tripleThd f i j k)
        (tripleSnd_comp_eq_tripleThd_comp f i j k)).hom =
      (overlapIso f ρ (tripleFst f i j k) (tripleThd f i j k)
        (tripleFst_comp_eq_tripleThd_comp f i j k)).hom

/-- **The isomorphism attached to `(h ≫ a, h ≫ b)` is the restriction along `h` of the one
attached to `(a, b)`**, through the comparisons of restriction along a composite. -/
theorem overlapIso_restrict {i j : ι} {W W' : X.C} (a : W ⟶ U i) (b : W ⟶ U j)
    (hab : a ≫ f i = b ≫ f j) (h : W' ⟶ W) {a' : W' ⟶ U i} (ha : h ≫ a = a')
    {b' : W' ⟶ U j} (hb : h ≫ b = b') (hab' : a' ≫ f i = b' ≫ f j) :
    (overlapIso f ρ a' b' hab').hom =
      (derivedOverMapComp.{0} X ha).hom.app (E i) ≫
        (derivedOverMap.{0} X h).map (overlapIso f ρ a b hab).hom ≫
          (derivedOverMapComp.{0} X hb).inv.app (E j) := by
  have hℓ : h ≫ pullback.lift a b hab = pullback.lift a' b' hab' := by
    apply pullback.hom_ext
    · rw [Category.assoc, pullback.lift_fst, pullback.lift_fst, ha]
    · rw [Category.assoc, pullback.lift_snd, pullback.lift_snd, hb]
  have assi := X.derivedOverMapComp_assoc (pullback.fst (f i) (f j)) (pullback.lift a b hab) h
    (pullback.lift_fst a b hab) hℓ ha (pullback.lift_fst a' b' hab') (E i)
  have assj := X.derivedOverMapComp_assoc (pullback.snd (f i) (f j)) (pullback.lift a b hab) h
    (pullback.lift_snd a b hab) hℓ hb (pullback.lift_snd a' b' hab') (E j)
  have nat := (derivedOverMapComp.{0} X hℓ).hom.naturality (ρ i j).hom
  simp only [Functor.comp_map] at nat
  -- the `j`-side, inverted
  have assj' : (derivedOverMap.{0} X h).map
        ((derivedOverMapComp.{0} X (pullback.lift_snd a b hab)).inv.app (E j)) ≫
        (derivedOverMapComp.{0} X hb).inv.app (E j) =
      (derivedOverMapComp.{0} X hℓ).inv.app
          ((derivedOverMap.{0} X (pullback.snd (f i) (f j))).obj (E j)) ≫
        (derivedOverMapComp.{0} X (pullback.lift_snd a' b' hab')).inv.app (E j) := by
    rw [← cancel_epi ((derivedOverMapComp.{0} X (pullback.lift_snd a' b' hab')).hom.app (E j) ≫
      (derivedOverMapComp.{0} X hℓ).hom.app
        ((derivedOverMap.{0} X (pullback.snd (f i) (f j))).obj (E j)))]
    conv_lhs => rw [← assj]
    simp only [Category.assoc, ← Functor.map_comp_assoc, Iso.hom_inv_id_app,
      Iso.hom_inv_id_app_assoc]
    simp
  simp only [overlapIso, Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom, Iso.symm_hom,
    Iso.app_inv, Functor.map_comp, Category.assoc]
  rw [assj', reassoc_of% assi, ← reassoc_of% nat, Iso.hom_inv_id_app_assoc]

/-- **The cocycle condition at an arbitrary object**: for arrows `a`, `b`, `c` from `W` to `U_i`,
`U_j`, `U_k` agreeing over `X`, the isomorphism attached to `(a, b)` followed by the one attached
to `(b, c)` is the one attached to `(a, c)`. -/
theorem overlapIso_trans (hρ : IsCocycle f ρ) {i j k : ι} {W : X.C} (a : W ⟶ U i)
    (b : W ⟶ U j) (c : W ⟶ U k) (hab : a ≫ f i = b ≫ f j) (hbc : b ≫ f j = c ≫ f k)
    (hac : a ≫ f i = c ≫ f k) :
    (overlapIso f ρ a b hab).hom ≫ (overlapIso f ρ b c hbc).hom =
      (overlapIso f ρ a c hac).hom := by
  let t : W ⟶ tripleOverlap f i j k :=
    pullback.lift (pullback.lift a b hab) c (by rw [pullback.lift_fst_assoc, hac])
  have ht1 : t ≫ tripleFst f i j k = a := by
    rw [tripleFst, pullback.lift_fst_assoc, pullback.lift_fst]
  have ht2 : t ≫ tripleSnd f i j k = b := by
    rw [tripleSnd, pullback.lift_fst_assoc, pullback.lift_snd]
  have ht3 : t ≫ tripleThd f i j k = c := by
    rw [tripleThd, pullback.lift_snd]
  rw [overlapIso_restrict f ρ _ _ (tripleFst_comp_eq_tripleSnd_comp f i j k) t ht1 ht2,
    overlapIso_restrict f ρ _ _ (tripleSnd_comp_eq_tripleThd_comp f i j k) t ht2 ht3,
    overlapIso_restrict f ρ _ _ (tripleFst_comp_eq_tripleThd_comp f i j k) t ht1 ht3,
    ← hρ i j k]
  simp only [Category.assoc, Iso.inv_hom_id_app_assoc, Functor.map_comp]

/-- The isomorphism attached to a pair `(a, a)` is the identity. -/
theorem overlapIso_self (hρ : IsCocycle f ρ) {i : ι} {W : X.C} (a : W ⟶ U i)
    (h : a ≫ f i = a ≫ f i) : (overlapIso f ρ a a h).hom = 𝟙 _ := by
  have := overlapIso_trans f ρ hρ a a a h h h
  rw [← cancel_mono (overlapIso f ρ a a h).hom, this, Category.id_comp]

/-- The isomorphisms attached to `(a, b)` and to `(b, a)` are mutually inverse. -/
theorem overlapIso_symm (hρ : IsCocycle f ρ) {i j : ι} {W : X.C} (a : W ⟶ U i) (b : W ⟶ U j)
    (hab : a ≫ f i = b ≫ f j) (hba : b ≫ f j = a ≫ f i) :
    (overlapIso f ρ a b hab).hom ≫ (overlapIso f ρ b a hba).hom = 𝟙 _ := by
  rw [overlapIso_trans f ρ hρ a b a hab hba rfl, overlapIso_self f ρ hρ]

omit [HasPullbacks X.C] in
/-- For an endomorphism `ℓ` of `V` equal to the identity, a morphism `r : A|_V ⟶ B|_V` restricted
along `ℓ` and conjugated by the comparisons of restriction along the composites `ℓ ≫ p = p` and
`ℓ ≫ q = q` is `r` again. -/
theorem derivedOverMapComp_id_conj {V U' U'' : X.C} {p : V ⟶ U'} {q : V ⟶ U''}
    {A : LocalDerivedCategory.{0} X U'} {B : LocalDerivedCategory.{0} X U''}
    (r : (derivedOverMap.{0} X p).obj A ⟶ (derivedOverMap.{0} X q).obj B) (ℓ : V ⟶ V)
    (hℓ : ℓ = 𝟙 V) (e₁ : ℓ ≫ p = p) (e₂ : ℓ ≫ q = q) :
    (derivedOverMapComp.{0} X e₁).hom.app A ≫ (derivedOverMap.{0} X ℓ).map r ≫
      (derivedOverMapComp.{0} X e₂).inv.app B = r := by
  subst hℓ
  have u₁ := X.derivedOverMapComp_hom_app_derivedOverMapIdIso p e₁ A
  have u₂ := X.derivedOverMapComp_hom_app_derivedOverMapIdIso q e₂ B
  have nat := (X.derivedOverMapIdIso V).hom.naturality r
  simp only [Functor.id_map] at nat
  have hc₁ : (derivedOverMapComp.{0} X e₁).hom.app A =
      (X.derivedOverMapIdIso V).inv.app ((derivedOverMap.{0} X p).obj A) := by
    rw [← cancel_mono ((X.derivedOverMapIdIso V).hom.app _), u₁, Iso.inv_hom_id_app]
    rfl
  have hc₂ : (derivedOverMapComp.{0} X e₂).inv.app B =
      (X.derivedOverMapIdIso V).hom.app ((derivedOverMap.{0} X q).obj B) := by
    rw [← cancel_epi ((derivedOverMapComp.{0} X e₂).hom.app B), Iso.hom_inv_id_app, u₂]
  rw [hc₁, hc₂, nat, Iso.inv_hom_id_app_assoc]

/-- On the fibre product `U_{ij}` itself, the isomorphism attached to the two projections is
`ρ_{ij}`. -/
theorem overlapIso_fst_snd (i j : ι) :
    (overlapIso f ρ (pullback.fst (f i) (f j)) (pullback.snd (f i) (f j))
      pullback.condition).hom = (ρ i j).hom :=
  derivedOverMapComp_id_conj (ρ i j).hom _ (by
    apply pullback.hom_ext
    · rw [pullback.lift_fst, Category.id_comp]
    · rw [pullback.lift_snd, Category.id_comp]) _ _

end AlgebraicGeometry.RingedSite.CoveringGlueing


namespace AlgebraicGeometry.RingedSite.CoveringGlueing

attribute [local instance] HasDerivedCategory.standard

variable {X : RingedSite.{u, u, u}} [HasPullbacks X.C] {X₀ : X.C} {ι : Type*} {U : ι → X.C}
  (f : ∀ i, U i ⟶ X₀)

/-- **The isomorphisms attached to two glueing data are compatible with a morphism of the
data.** If `β_i : E'_i ⟶ E_i` carries `ρ'_{ij}` to `ρ_{ij}` on the overlaps, then it carries the
isomorphism attached to `(a, b)` for `ρ'` to the one for `ρ`. -/
theorem overlapIso_naturality {E E' : ∀ i, LocalDerivedCategory.{0} X (U i)}
    (ρ : ∀ i j, (derivedOverMap.{0} X (pullback.fst (f i) (f j))).obj (E i) ≅
      (derivedOverMap.{0} X (pullback.snd (f i) (f j))).obj (E j))
    (ρ' : ∀ i j, (derivedOverMap.{0} X (pullback.fst (f i) (f j))).obj (E' i) ≅
      (derivedOverMap.{0} X (pullback.snd (f i) (f j))).obj (E' j))
    (β : ∀ i, E' i ⟶ E i)
    (hβ : ∀ i j, (derivedOverMap.{0} X (pullback.fst (f i) (f j))).map (β i) ≫ (ρ i j).hom =
      (ρ' i j).hom ≫ (derivedOverMap.{0} X (pullback.snd (f i) (f j))).map (β j))
    {i j : ι} {W : X.C} (a : W ⟶ U i) (b : W ⟶ U j) (hab : a ≫ f i = b ≫ f j) :
    (derivedOverMap.{0} X a).map (β i) ≫ (overlapIso f ρ a b hab).hom =
      (overlapIso f ρ' a b hab).hom ≫ (derivedOverMap.{0} X b).map (β j) := by
  have n1 := (derivedOverMapComp.{0} X (pullback.lift_fst a b hab)).hom.naturality (β i)
  have n2 := (derivedOverMapComp.{0} X (pullback.lift_snd a b hab)).inv.naturality (β j)
  simp only [Functor.comp_map] at n1 n2
  simp only [overlapIso, Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom, Iso.symm_hom,
    Iso.app_inv, Category.assoc]
  rw [reassoc_of% n1, ← Functor.map_comp_assoc, hβ, Functor.map_comp_assoc, n2]

/-- **The canonical glueing data of a global object**: the two restrictions of `N` to `U_{ij}`
are both its restriction along the composite `U_{ij} ⟶ X`. -/
def canonicalOverlap (N : LocalDerivedCategory.{0} X X₀) (i j : ι) :
    (derivedOverMap.{0} X (pullback.fst (f i) (f j))).obj ((derivedOverMap.{0} X (f i)).obj N) ≅
      (derivedOverMap.{0} X (pullback.snd (f i) (f j))).obj ((derivedOverMap.{0} X (f j)).obj N) :=
  ((derivedOverMapComp.{0} X (rfl : pullback.fst (f i) (f j) ≫ f i = _)).app N).symm ≪≫
    (derivedOverMapComp.{0} X (pullback.condition (f := f i) (g := f j)).symm).app N

/-- **The isomorphisms attached to the canonical glueing data are canonical**: at `(a, b)` it is
the comparison of the two restrictions of `N` along the common composite `W ⟶ X`. -/
theorem overlapIso_canonicalOverlap (N : LocalDerivedCategory.{0} X X₀) {i j : ι} {W : X.C}
    (a : W ⟶ U i) (b : W ⟶ U j) (hab : a ≫ f i = b ≫ f j) :
    overlapIso f (canonicalOverlap f N) a b hab =
      ((derivedOverMapComp.{0} X (rfl : a ≫ f i = a ≫ f i)).app N).symm ≪≫
        (derivedOverMapComp.{0} X hab.symm).app N := by
  have e3 : pullback.lift a b hab ≫ pullback.fst (f i) (f j) ≫ f i = a ≫ f i := by
    rw [pullback.lift_fst_assoc]
  have A1 := X.derivedOverMapComp_assoc (f i) (pullback.fst (f i) (f j)) (pullback.lift a b hab)
    (rfl : pullback.fst (f i) (f j) ≫ f i = _) (pullback.lift_fst a b hab) e3
    (rfl : a ≫ f i = a ≫ f i) N
  have A2 := X.derivedOverMapComp_assoc (f j) (pullback.snd (f i) (f j)) (pullback.lift a b hab)
    (pullback.condition (f := f i) (g := f j)).symm (pullback.lift_snd a b hab) e3 hab.symm N
  ext
  simp only [overlapIso, canonicalOverlap, Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom,
    Iso.symm_hom, Iso.app_inv, Functor.map_comp, Category.assoc]
  rw [← cancel_epi ((derivedOverMapComp.{0} X (rfl : a ≫ f i = a ≫ f i)).hom.app N),
    Iso.hom_inv_id_app_assoc, ← reassoc_of% A1, ← Functor.map_comp_assoc, Iso.hom_inv_id_app,
    CategoryTheory.Functor.map_id, Category.id_comp, reassoc_of% A2, Iso.hom_inv_id_app,
    Category.comp_id]

omit [HasPullbacks X.C] in
/-- The comparisons of restriction along a composite, for two presentations of the composite. -/
theorem derivedOverMapComp_hom_app_eq_eqToHom_comp {U' V W : X.C} {g : V ⟶ U'} {h : W ⟶ V}
    {k k' : W ⟶ U'} (e : h ≫ g = k) (e' : h ≫ g = k') (N : LocalDerivedCategory.{0} X U') :
    (derivedOverMapComp.{0} X e').hom.app N =
      eqToHom (by rw [← e, ← e']) ≫ (derivedOverMapComp.{0} X e).hom.app N := by
  subst e e'
  simp

/-- **The canonical glueing data of a global object satisfy the cocycle condition.** -/
theorem isCocycle_canonicalOverlap (N : LocalDerivedCategory.{0} X X₀) :
    IsCocycle f (canonicalOverlap f N) := by
  intro i j k
  simp only [overlapIso_canonicalOverlap, Iso.trans_hom, Iso.symm_hom, Iso.app_inv, Iso.app_hom,
    Category.assoc]
  rw [derivedOverMapComp_hom_app_eq_eqToHom_comp
      (rfl : tripleSnd f i j k ≫ f j = tripleSnd f i j k ≫ f j)
      (tripleFst_comp_eq_tripleSnd_comp f i j k).symm,
    derivedOverMapComp_hom_app_eq_eqToHom_comp (tripleSnd_comp_eq_tripleThd_comp f i j k).symm
      (tripleFst_comp_eq_tripleThd_comp f i j k).symm]
  simp

/-- For arrows `a : W ⟶ U_i` and `b : W ⟶ U_j` over `X` and `k : W' ⟶ W`, the canonical
comparison `N|_{U_i}|_W|_{W'} ⟶ N|_{U_j}|_{W'}` of restrictions of a global object, as a natural
transformation in the global object. -/
def canonicalRestrictionComparison {i j : ι} {W W' : X.C} (a : W ⟶ U i) (k : W' ⟶ W)
    (b : W' ⟶ U j) (hab : (k ≫ a) ≫ f i = b ≫ f j) :
    derivedOverMap.{0} X (f i) ⋙ derivedOverMap.{0} X a ⋙ derivedOverMap.{0} X k ⟶
      derivedOverMap.{0} X (f j) ⋙ derivedOverMap.{0} X b :=
  Functor.whiskerLeft (derivedOverMap.{0} X (f i))
      (derivedOverMapComp.{0} X (rfl : k ≫ a = k ≫ a)).inv ≫
    (derivedOverMapComp.{0} X (rfl : (k ≫ a) ≫ f i = (k ≫ a) ≫ f i)).inv ≫
      (derivedOverMapComp.{0} X hab.symm).hom

/-- The canonical comparison is the restriction along `k` followed by the isomorphism attached to
`(k ≫ a, b)` for the canonical glueing data. -/
theorem canonicalRestrictionComparison_app {i j : ι} {W W' : X.C} (a : W ⟶ U i) (k : W' ⟶ W)
    (b : W' ⟶ U j) (hab : (k ≫ a) ≫ f i = b ≫ f j) (N : LocalDerivedCategory.{0} X X₀) :
    (canonicalRestrictionComparison f a k b hab).app N =
      (derivedOverMapComp.{0} X (rfl : k ≫ a = k ≫ a)).inv.app
          ((derivedOverMap.{0} X (f i)).obj N) ≫
        (overlapIso f (canonicalOverlap f N) (k ≫ a) b hab).hom := by
  rw [overlapIso_canonicalOverlap]
  rfl

omit [HasPullbacks X.C] in
/-- The inverse comparison of derived restrictions along a composite is induced by the inverse
comparison of restrictions of sheaves of modules. -/
theorem derivedOverMapComp_inv_isInducedBy {U' V W : X.C} {g : V ⟶ U'} {h : W ⟶ V} {k : W ⟶ U'}
    (e : h ≫ g = k) :
    NatTrans.IsInducedBy
      (Functor.compFactorization (X.derivedOverMapFactors g) (X.derivedOverMapFactors h))
      (X.derivedOverMapFactors k) (derivedOverMapComp.{0} X e).inv
      (Functor.mapHomologicalComplexCompIso (X.overMapCompInv e).symm (ComplexShape.up ℤ)).hom :=
  NatTrans.IsInducedBy.inv (γ := derivedOverMapComp.{0} X e)
    (γ₀ := (Functor.mapHomologicalComplexCompIso (X.overMapCompInv e).symm
      (ComplexShape.up ℤ)).symm)
    (X.derivedOverMapComp_hom_isInducedBy e)

omit [HasPullbacks X.C] in
/-- The canonical comparison of restrictions is induced by comparisons of restrictions of sheaves
of modules. -/
theorem canonicalRestrictionComparison_isInducedBy {i j : ι} {W W' : X.C} (a : W ⟶ U i)
    (k : W' ⟶ W) (b : W' ⟶ U j) (hab : (k ≫ a) ≫ f i = b ≫ f j) :
    NatTrans.IsInducedBy
      (Functor.compFactorization (X.derivedOverMapFactors (f i))
        (Functor.compFactorization (X.derivedOverMapFactors a) (X.derivedOverMapFactors k)))
      (Functor.compFactorization (X.derivedOverMapFactors (f j)) (X.derivedOverMapFactors b))
      (canonicalRestrictionComparison f a k b hab)
      (Functor.whiskerLeft ((X.overMapModules (f i)).mapHomologicalComplex (ComplexShape.up ℤ))
          (Functor.mapHomologicalComplexCompIso (X.overMapCompInv (rfl : k ≫ a = k ≫ a)).symm
            (ComplexShape.up ℤ)).hom ≫
        (Functor.mapHomologicalComplexCompIso
          (X.overMapCompInv (rfl : (k ≫ a) ≫ f i = (k ≫ a) ≫ f i)).symm
            (ComplexShape.up ℤ)).hom ≫
        (Functor.mapHomologicalComplexCompIso (X.overMapCompInv hab.symm).symm
          (ComplexShape.up ℤ)).inv) := by
  have h1 := NatTrans.IsInducedBy.whiskerLeft (X.derivedOverMapFactors (f i))
    (derivedOverMapComp_inv_isInducedBy (X := X) (rfl : k ≫ a = k ≫ a))
  have h2 := derivedOverMapComp_inv_isInducedBy (X := X)
    (rfl : (k ≫ a) ≫ f i = (k ≫ a) ≫ f i)
  have h3 := X.derivedOverMapComp_hom_isInducedBy hab.symm
  exact h1.comp (h2.comp h3)

end AlgebraicGeometry.RingedSite.CoveringGlueing

end
