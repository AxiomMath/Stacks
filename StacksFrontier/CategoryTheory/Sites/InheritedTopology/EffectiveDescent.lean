module

public import StacksFrontier.CategoryTheory.Sites.InheritedTopology.Defs
public import StacksFrontier.CategoryTheory.Sites.InheritedTopology.Stack
import StacksFrontier.CategoryTheory.Sites.InheritedTopology.Pullback
import StacksFrontier.CategoryTheory.Sites.InheritedTopology.Transport

/-! # Effective descent for an inherited topology

Let `(𝒞, J)` be a site, let `p : 𝒳 ⥤ 𝒞` and `q : 𝒴 ⥤ 𝒞` be stacks in groupoids and let
`F : 𝒳 ⥤ 𝒴` be a 1-morphism of categories over `𝒞` making `𝒳` fibred in groupoids over
`𝒴`. This file proves that every descent datum in `𝒳` relative to a covering family of
the topology inherited from `(𝒞, J)` is effective, which is condition (3) of Stacks
06NX.

A descent datum over `𝒴` is also a descent datum over `𝒞` for the descended covering
family, so it is effective there. The resulting object lies over `q.obj U`, and the
`Isom` sheaf condition for `q` glues the `F`-images of its comparison isomorphisms into
an isomorphism onto `U`; lifting that isomorphism through `F` moves the object into the
fibre over `U`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe w v₁ u₁ v₂ u₂ v₃ u₃

namespace CategoryTheory.Functor

variable {𝒞 : Type u₁} {𝒳 : Type u₂} {𝒴 : Type u₃}
  [Category.{v₁} 𝒞] [Category.{v₂} 𝒳] [Category.{v₃} 𝒴]

/-- The canonical comparison `Restriction.compTo` lies over the base morphism it is taken
along. -/
private theorem compTo_isHomLift {C S : Type*} [Category C] [Category S] (p : S ⥤ C)
    {W V U : C} (g : W ⟶ V) (f : V ⟶ U) {h : W ⟶ U} (hh : h = g ≫ f) {x : S}
    {hx : p.obj x = U} (xr : Restriction p f x hx) (xrW : Restriction p h x hx) :
    p.IsHomLift (eqToHom xrW.hpt ≫ g ≫ eqToHom xr.hpt.symm) (Restriction.compTo p g f hh xr xrW) :=
  have hpre : p.IsHomLift ((eqToHom xrW.hpt ≫ g ≫ eqToHom xr.hpt.symm) ≫
      (eqToHom xr.hpt ≫ f ≫ eqToHom hx.symm)) xrW.hom := by
    have e : (eqToHom xrW.hpt ≫ g ≫ eqToHom xr.hpt.symm) ≫ (eqToHom xr.hpt ≫ f ≫ eqToHom hx.symm)
        = eqToHom xrW.hpt ≫ h ≫ eqToHom hx.symm := by subst hh; simp
    rw [e]; exact xrW.isHomLift
  Functor.IsStronglyCartesian.map_isHomLift p
    (eqToHom xr.hpt ≫ f ≫ eqToHom hx.symm) xr.hom rfl xrW.hom

/-- The image under the base functor of `Restriction.compTo` is the base morphism it is taken
along. -/
private theorem map_compTo {C S : Type*} [Category C] [Category S] (p : S ⥤ C)
    {W V U : C} (g : W ⟶ V) (f : V ⟶ U) {h : W ⟶ U} (hh : h = g ≫ f) {x : S}
    {hx : p.obj x = U} (xr : Restriction p f x hx) (xrW : Restriction p h x hx) :
    p.map (Restriction.compTo p g f hh xr xrW) = eqToHom xrW.hpt ≫ g ≫ eqToHom xr.hpt.symm := by
  have := compTo_isHomLift p g f hh xr xrW
  simpa using IsHomLift.fac' p (eqToHom xrW.hpt ≫ g ≫ eqToHom xr.hpt.symm)
    (Restriction.compTo p g f hh xr xrW)

/-- The comparison from a restriction along `g` to the trivial restriction is its `hom`. -/
private theorem compTo_id_eq_hom {C S : Type*} [Category C] [Category S] (p : S ⥤ C)
    {W V : C} (g : W ⟶ V) {x : S} {hx : p.obj x = V} (xrW : Restriction p g x hx) :
    Restriction.compTo p g (𝟙 V) (Category.comp_id g).symm (Restriction.id p x hx) xrW
      = xrW.hom :=
  (Category.comp_id _).symm.trans
    (Restriction.compTo_hom p g (𝟙 V) (Category.comp_id g).symm (Restriction.id p x hx) xrW)

/-- The base image of the `hom` of a restriction is the base morphism it lies over. -/
private theorem map_restriction_hom {C S : Type*} [Category C] [Category S] (p : S ⥤ C)
    {V U : C} (f : V ⟶ U) {x : S} {hx : p.obj x = U} (xr : Restriction p f x hx) :
    p.map xr.hom = eqToHom xr.hpt ≫ f ≫ eqToHom hx.symm := by
  simpa using IsHomLift.fac' p (eqToHom xr.hpt ≫ f ≫ eqToHom hx.symm) xr.hom

/-- The base image of a fibre morphism is a composite of identities of the base. -/
private theorem map_eq_of_fibreHom {C S : Type*} [Category C] [Category S] (p : S ⥤ C) {U : C}
    {a b : S} {ha : p.obj a = U} {hb : p.obj b = U} {φ : a ⟶ b} (h : FibreHom p a b ha hb φ) :
    p.map φ = eqToHom ha ≫ eqToHom hb.symm := by
  simpa using IsHomLift.fac' p (eqToHom ha ≫ eqToHom hb.symm) φ

/-- In a category fibred in groupoids, a morphism with invertible base image is invertible. -/
private theorem isIso_of_isIso_map {C S : Type*} [Category C] [Category S] {p : S ⥤ C}
    (hp : p.IsFiberedInGroupoids) {a b : S} (φ : a ⟶ b) [IsIso (p.map φ)] : IsIso φ :=
  haveI := hp.isStronglyCartesian φ
  Functor.IsStronglyCartesian.isIso_of_base_isIso p (p.map φ) φ

/-- In a category fibred in groupoids, two parallel morphisms with the same base image agree
once they agree after composing with a further morphism. -/
private theorem eq_of_map_eq_of_comp_eq {C S : Type*} [Category C] [Category S] {q : S ⥤ C}
    (hq : q.IsFiberedInGroupoids) {a b c : S} (h : b ⟶ c) {u g : a ⟶ b}
    (hu : q.map u = q.map g) (hpost : u ≫ h = g ≫ h) : u = g :=
  haveI := hq.isStronglyCartesian h
  haveI : q.IsHomLift (q.map g) g := CategoryTheory.IsHomLift.map q g
  haveI : q.IsHomLift (q.map g) u := hu ▸ CategoryTheory.IsHomLift.map q u
  Functor.IsStronglyCartesian.ext (p := q) (q.map h) h (g := q.map g) hpost

/-- **Condition (3) of Stacks 06NX.** For stacks in groupoids `p` and `q` over a site
`(𝒞, J)` and a 1-morphism `F` over `𝒞` making `𝒳` fibred in groupoids over `𝒴`, every
descent datum in `𝒳` relative to a covering family of the inherited topology on `𝒴` is
effective.

The datum is read as a descent datum over the base `𝒞` relative to the descended
covering family `{ q.map (f i) }`, and descended there using that `p` is a stack in
groupoids. This produces an object `x₀` over `q.obj U`; the images under `F` of the
comparison isomorphisms then glue, by the `Isom` sheaf condition for `q`, to an
isomorphism `F.obj x₀ ⟶ U` in `𝒴`, and lifting it through `F` replaces `x₀` by an
object lying over `U`. -/
theorem effective_descent_of_isFiberedInGroupoids
    (J : GrothendieckTopology 𝒞) (J𝒴 : GrothendieckTopology 𝒴)
    (p : 𝒳 ⥤ 𝒞) (q : 𝒴 ⥤ 𝒞) (F : 𝒳 ⥤ 𝒴)
    (hp : IsStackInGroupoids.{w} p J) (hq : IsStackInGroupoids.{w} q J)
    (hF₁ : F ⋙ q = p)
    (hF₂ : F.IsFiberedInGroupoids)
    (hJ𝒴 : IsInheritedTopology.{w} q J J𝒴)
    {U : 𝒴} {I : Type w} (V : I → 𝒴) (f : ∀ i, V i ⟶ U)
    (hf : Sieve.ofArrows V f ∈ J𝒴 U)
    (Vij : I → I → 𝒴)
    (pr₁ : ∀ i j, Vij i j ⟶ V i) (pr₂ : ∀ i j, Vij i j ⟶ V j)
    (hVij : ∀ i j, IsPullback (pr₁ i j) (pr₂ i j) (f i) (f j))
    (Vijk : I → I → I → 𝒴)
    (s₁₂ : ∀ i j k, Vijk i j k ⟶ Vij i j) (s₂₃ : ∀ i j k, Vijk i j k ⟶ Vij j k)
    (hVijk : ∀ i j k, IsPullback (s₁₂ i j k) (s₂₃ i j k) (pr₂ i j) (pr₁ j k))
    (q₁ : ∀ i j k, Vijk i j k ⟶ V i) (q₂ : ∀ i j k, Vijk i j k ⟶ V j)
    (q₃ : ∀ i j k, Vijk i j k ⟶ V k)
    (hq₁ : ∀ i j k, q₁ i j k = s₁₂ i j k ≫ pr₁ i j)
    (hq₂ : ∀ i j k, q₂ i j k = s₁₂ i j k ≫ pr₂ i j)
    (hq₃ : ∀ i j k, q₃ i j k = s₂₃ i j k ≫ pr₂ j k)
    (D : DescentDatum F V f Vij pr₁ pr₂ hVij Vijk s₁₂ s₂₃ hVijk q₁ q₂ q₃ hq₁ hq₂ hq₃) :
    D.IsEffective := by
  set c₀ := q.obj U with hc₀
  -- Every arrow of 𝒴 is q-strongly cartesian, in particular each `f i`.
  have hf_cart : ∀ i, q.IsStronglyCartesian (q.map (f i)) (f i) :=
    fun i => hq.isFiberedInGroupoids.isStronglyCartesian (f i)
  -- `{q.map (f i)}` is a J-cover of `c₀`.
  have hcov𝒞 : Sieve.ofArrows (fun i => q.obj (V i)) (fun i => q.map (f i)) ∈ J c₀ :=
    (hJ𝒴 V f hf_cart).mp hf
  -- `q` is fibred in groupoids.
  have hqfib := hq.isFiberedInGroupoids
  -- `D.x i` lies over `q.obj (V i)` for `p = F ⋙ q`.
  have hxp : ∀ i, p.obj (D.x i) = q.obj (V i) := fun i => by
    rw [← hF₁]; exact congrArg q.obj (D.hx i)
  -- The `q`-image of an `F`-image is the `p`-image, up to `F ⋙ q = p`.
  have hqF : ∀ {a b : 𝒳} (x : a ⟶ b), q.map (F.map x) =
      eqToHom (Functor.congr_obj hF₁ a) ≫ p.map x ≫ eqToHom (Functor.congr_obj hF₁ b).symm :=
    fun x => Functor.congr_hom hF₁ x
  -- An object over `c` for `p` is over `c` for `q` after applying `F`.
  have hqFobj : ∀ {a : 𝒳} {c : 𝒞}, p.obj a = c → q.obj (F.obj a) = c :=
    fun h => (Functor.congr_obj hF₁ _).trans h
  -- The 𝒞-side double overlaps, obtained by applying `q` to the 𝒴-pullbacks.
  set Vij' : I → I → 𝒞 := fun i j => q.obj (Vij i j) with hVij'def
  set pr₁' : ∀ i j, Vij' i j ⟶ q.obj (V i) := fun i j => q.map (pr₁ i j) with hpr₁'def
  set pr₂' : ∀ i j, Vij' i j ⟶ q.obj (V j) := fun i j => q.map (pr₂ i j) with hpr₂'def
  have hVijC : ∀ i j, IsPullback (pr₁' i j) (pr₂' i j) (q.map (f i)) (q.map (f j)) :=
    fun i j => hqfib.isPullback_map (f i) (f j) (pr₁ i j) (pr₂ i j) (hVij i j)
  -- The 𝒞-side triple overlaps.
  set Vijk' : I → I → I → 𝒞 := fun i j k => q.obj (Vijk i j k) with hVijk'def
  set s₁₂' : ∀ i j k, Vijk' i j k ⟶ Vij' i j := fun i j k => q.map (s₁₂ i j k) with hs₁₂'def
  set s₂₃' : ∀ i j k, Vijk' i j k ⟶ Vij' j k := fun i j k => q.map (s₂₃ i j k) with hs₂₃'def
  have hVijkC : ∀ i j k, IsPullback (s₁₂' i j k) (s₂₃' i j k) (pr₂' i j) (pr₁' j k) :=
    fun i j k => hqfib.isPullback_map (pr₂ i j) (pr₁ j k)
      (s₁₂ i j k) (s₂₃ i j k) (hVijk i j k)
  set q₁' : ∀ i j k, Vijk' i j k ⟶ q.obj (V i) := fun i j k => q.map (q₁ i j k) with hq₁'def
  set q₂' : ∀ i j k, Vijk' i j k ⟶ q.obj (V j) := fun i j k => q.map (q₂ i j k) with hq₂'def
  set q₃' : ∀ i j k, Vijk' i j k ⟶ q.obj (V k) := fun i j k => q.map (q₃ i j k) with hq₃'def
  have hq₁' : ∀ i j k, q₁' i j k = s₁₂' i j k ≫ pr₁' i j := fun i j k => by
    simp [hq₁'def, hs₁₂'def, hpr₁'def, hq₁ i j k]
  have hq₂' : ∀ i j k, q₂' i j k = s₁₂' i j k ≫ pr₂' i j := fun i j k => by
    simp [hq₂'def, hs₁₂'def, hpr₂'def, hq₂ i j k]
  have hq₃' : ∀ i j k, q₃' i j k = s₂₃' i j k ≫ pr₂' j k := fun i j k => by
    simp [hq₃'def, hs₂₃'def, hpr₂'def, hq₃ i j k]
  -- Cartesianness of the various projections.
  have hpr₁_cart : ∀ i j, q.IsStronglyCartesian (q.map (pr₁ i j)) (pr₁ i j) :=
    fun i j => hqfib.isStronglyCartesian (pr₁ i j)
  have hpr₂_cart : ∀ i j, q.IsStronglyCartesian (q.map (pr₂ i j)) (pr₂ i j) :=
    fun i j => hqfib.isStronglyCartesian (pr₂ i j)
  have hq₁_cart : ∀ i j k, q.IsStronglyCartesian (q.map (q₁ i j k)) (q₁ i j k) :=
    fun i j k => hqfib.isStronglyCartesian (q₁ i j k)
  have hq₂_cart : ∀ i j k, q.IsStronglyCartesian (q.map (q₂ i j k)) (q₂ i j k) :=
    fun i j k => hqfib.isStronglyCartesian (q₂ i j k)
  have hq₃_cart : ∀ i j k, q.IsStronglyCartesian (q.map (q₃ i j k)) (q₃ i j k) :=
    fun i j k => hqfib.isStronglyCartesian (q₃ i j k)
  -- The restrictions read over 𝒞, with the same `pt` and `hom` as the `F`-ones.
  set Dpxrij : ∀ i j, Restriction p (pr₁' i j) (D.x i) (hxp i) := fun i j =>
    Restriction.ofCompEq p q F hF₁ (pr₁ i j) (hpr₁_cart i j) (D.x i) (D.hx i) (D.xrij i j)
    with hDpxrij
  set Dpxrji : ∀ i j, Restriction p (pr₂' i j) (D.x j) (hxp j) := fun i j =>
    Restriction.ofCompEq p q F hF₁ (pr₂ i j) (hpr₂_cart i j) (D.x j) (D.hx j) (D.xrji i j)
    with hDpxrji
  set Dpwi : ∀ i j k, Restriction p (q₁' i j k) (D.x i) (hxp i) := fun i j k =>
    Restriction.ofCompEq p q F hF₁ (q₁ i j k) (hq₁_cart i j k) (D.x i) (D.hx i) (D.wi i j k)
    with hDpwi
  set Dpwj : ∀ i j k, Restriction p (q₂' i j k) (D.x j) (hxp j) := fun i j k =>
    Restriction.ofCompEq p q F hF₁ (q₂ i j k) (hq₂_cart i j k) (D.x j) (D.hx j) (D.wj i j k)
    with hDpwj
  set Dpwk : ∀ i j k, Restriction p (q₃' i j k) (D.x k) (hxp k) := fun i j k =>
    Restriction.ofCompEq p q F hF₁ (q₃ i j k) (hq₃_cart i j k) (D.x k) (D.hx k) (D.wk i j k)
    with hDpwk
  -- A fibre morphism for `F` is a fibre morphism for `p`, on the same 𝒳-arrow.
  -- The `αij`, `αjk`, `αik` restriction fields of the descended datum.
  have hαij_restr : ∀ i j k,
      IsRestrictionOf p (s₁₂' i j k) (hq₁' i j k) (hq₂' i j k) (Dpxrij i j) (Dpxrji i j)
        (Dpwi i j k) (Dpwj i j k) (D.φ i j) (D.αij i j k) := by
    intro i j k
    have hcF := D.αij_restr i j k
    unfold IsRestrictionOf
    rw [Restriction.compTo_ofCompEq p q F hF₁ (s₁₂ i j k) (pr₂ i j) (hq₂ i j k)
          (hpr₂_cart i j) (hq₂_cart i j k) (D.x j) (D.hx j) (D.xrji i j) (D.wj i j k),
        Restriction.compTo_ofCompEq p q F hF₁ (s₁₂ i j k) (pr₁ i j) (hq₁ i j k)
          (hpr₁_cart i j) (hq₁_cart i j k) (D.x i) (D.hx i) (D.xrij i j) (D.wi i j k)]
    exact hcF
  have hαjk_restr : ∀ i j k,
      IsRestrictionOf p (s₂₃' i j k) ((hq₂' i j k).trans (hVijkC i j k).w) (hq₃' i j k)
        (Dpxrij j k) (Dpxrji j k) (Dpwj i j k) (Dpwk i j k) (D.φ j k) (D.αjk i j k) := by
    intro i j k
    have hcF := D.αjk_restr i j k
    unfold IsRestrictionOf
    rw [Restriction.compTo_ofCompEq p q F hF₁ (s₂₃ i j k) (pr₂ j k) (hq₃ i j k)
          (hpr₂_cart j k) (hq₃_cart i j k) (D.x k) (D.hx k) (D.xrji j k) (D.wk i j k),
        Restriction.compTo_ofCompEq p q F hF₁ (s₂₃ i j k) (pr₁ j k)
          ((hq₂ i j k).trans (hVijk i j k).w)
          (hpr₁_cart j k) (hq₂_cart i j k) (D.x j) (D.hx j) (D.xrij j k) (D.wj i j k)]
    exact hcF
  have hαik_restr : ∀ i j k,
      IsRestrictionOf p (q.map (D.s₁₃ i j k))
        (show q₁' i j k = q.map (D.s₁₃ i j k) ≫ pr₁' i k from by
          simp [hq₁'def, hpr₁'def, ← q.map_comp, D.hs₁₃₁ i j k])
        (show q₃' i j k = q.map (D.s₁₃ i j k) ≫ pr₂' i k from by
          simp [hq₃'def, hpr₂'def, ← q.map_comp, D.hs₁₃₂ i j k])
        (Dpxrij i k) (Dpxrji i k) (Dpwi i j k) (Dpwk i j k) (D.φ i k) (D.αik i j k) := by
    intro i j k
    have hcF := D.αik_restr i j k
    unfold IsRestrictionOf
    rw [Restriction.compTo_ofCompEq p q F hF₁ (D.s₁₃ i j k) (pr₂ i k) (D.hs₁₃₂ i j k).symm
          (hpr₂_cart i k) (hq₃_cart i j k) (D.x k) (D.hx k) (D.xrji i k) (D.wk i j k),
        Restriction.compTo_ofCompEq p q F hF₁ (D.s₁₃ i j k) (pr₁ i k) (D.hs₁₃₁ i j k).symm
          (hpr₁_cart i k) (hq₁_cart i j k) (D.x i) (D.hx i) (D.xrij i k) (D.wi i j k)]
    exact hcF
  have hs₁₃₁' : ∀ i j k, q.map (D.s₁₃ i j k) ≫ pr₁' i k = q₁' i j k := fun i j k => by
    simp [hpr₁'def, hq₁'def, ← q.map_comp, D.hs₁₃₁ i j k]
  have hs₁₃₂' : ∀ i j k, q.map (D.s₁₃ i j k) ≫ pr₂' i k = q₃' i j k := fun i j k => by
    simp [hpr₂'def, hq₃'def, ← q.map_comp, D.hs₁₃₂ i j k]
  -- Assemble the descent datum over the base 𝒞.
  set Dp : DescentDatum p (fun i => q.obj (V i)) (fun i => q.map (f i))
      Vij' pr₁' pr₂' hVijC Vijk' s₁₂' s₂₃' hVijkC q₁' q₂' q₃' hq₁' hq₂' hq₃' :=
    { x := D.x
      hx := hxp
      xrij := Dpxrij
      xrji := Dpxrji
      φ := D.φ
      φ_fibreHom := fun i j =>
        FibreHom.ofCompEq hF₁ (D.xrij i j).hpt (D.xrji i j).hpt (Dpxrij i j).hpt
          (Dpxrji i j).hpt (D.φ i j) (D.φ_fibreHom i j)
      φ_iso := D.φ_iso
      wi := Dpwi
      wj := Dpwj
      wk := Dpwk
      αij := D.αij
      αjk := D.αjk
      αik := D.αik
      αij_restr := hαij_restr
      αjk_restr := hαjk_restr
      s₁₃ := fun i j k => q.map (D.s₁₃ i j k)
      hs₁₃₁ := hs₁₃₁'
      hs₁₃₂ := hs₁₃₂'
      αik_restr := hαik_restr
      cocycle := D.cocycle }
    with hDp
  -- Descend it, using that `p` is a stack in groupoids.
  have hDp_eff : Dp.IsEffective :=
    hp.effective_descent (fun i => q.obj (V i)) (fun i => q.map (f i)) hcov𝒞
      Vij' pr₁' pr₂' hVijC Vijk' s₁₂' s₂₃' hVijkC q₁' q₂' q₃' hq₁' hq₂' hq₃' Dp
  obtain ⟨x₀, hx₀p, pxr, ψ, hψ_fib, hψ_iso, hψ_compat⟩ := hDp_eff
  -- Promote `x₀`, which lies over `c₀` for `p`, to a witness lying over `U` for `F`.
  have hx₀q : q.obj (F.obj x₀) = c₀ := hqFobj hx₀p
  -- Every arrow of 𝒴 is q-strongly cartesian.
  have hqcart : ∀ {a b : 𝒴} (g : a ⟶ b), q.IsStronglyCartesian (q.map g) g :=
    fun {a b} g => hqfib.isStronglyCartesian g
  have hFpxr_qobj : ∀ i, q.obj (F.obj (pxr i).pt) = q.obj (V i) := fun i => hqFobj (pxr i).hpt
  have hpψ : ∀ i, p.map (ψ i) = eqToHom (pxr i).hpt ≫ eqToHom (hxp i).symm :=
    fun i => map_eq_of_fibreHom p (hψ_fib i)
  have hqFpxr_map : ∀ i, q.map (F.map (pxr i).hom)
      = eqToHom (hFpxr_qobj i) ≫ q.map (f i) ≫ eqToHom hx₀q.symm := by
    intro i
    have hpmap := map_restriction_hom p _ (pxr i)
    rw [hqF (pxr i).hom, hpmap]
    simp [eqToHom_trans]
  -- The q-restriction of `F.obj x₀` along `q.map (f i)`, via `F.map (pxr i).hom`.
  set qxr : ∀ i, Restriction q (q.map (f i)) (F.obj x₀) hx₀q := fun i =>
    { pt := F.obj (pxr i).pt
      hpt := hFpxr_qobj i
      hom := F.map (pxr i).hom
      isHomLift := by
        refine CategoryTheory.IsHomLift.of_commsq q _ _ rfl rfl ?_
        rw [hqFpxr_map i]; simp
      isCart := by
        have h := hqcart (F.map (pxr i).hom)
        rw [hqFpxr_map i] at h
        exact h }
    with hqxr
  -- The q-restriction of `U` along `q.map (f i)`, via `f i`.
  set qyr : ∀ i, Restriction q (q.map (f i)) U (rfl : q.obj U = q.obj U) := fun i =>
    { pt := V i
      hpt := rfl
      hom := f i
      isHomLift := by
        have e : (eqToHom (rfl : q.obj (V i) = q.obj (V i)) ≫ q.map (f i) ≫
            eqToHom (rfl : q.obj U = q.obj U).symm) = q.map (f i) := by simp
        rw [e]; exact CategoryTheory.IsHomLift.map q (f i)
      isCart := by
        have e : (eqToHom (rfl : q.obj (V i) = q.obj (V i)) ≫ q.map (f i) ≫
            eqToHom (rfl : q.obj U = q.obj U).symm) = q.map (f i) := by simp
        rw [e]; exact hqcart (f i) }
    with hqyr
  -- The gluing family `sφ i : F.obj (pxr i).pt ⟶ V i`.
  have hψF_cod : ∀ i, F.obj (D.x i) = V i := D.hx
  set sφ : ∀ i, (qxr i).pt ⟶ (qyr i).pt := fun i =>
    F.map (ψ i) ≫ eqToHom (hψF_cod i) with hsφ
  -- Chosen q-restrictions over the overlaps.
  set qxrij : ∀ i j, Restriction q (pr₁' i j ≫ q.map (f i)) (F.obj x₀) hx₀q := fun i j =>
    Restriction.ofIsFiberedInGroupoids q hqfib (pr₁' i j ≫ q.map (f i)) (F.obj x₀) hx₀q with hqxrij
  set qyrij : ∀ i j, Restriction q (pr₁' i j ≫ q.map (f i)) U (rfl : q.obj U = q.obj U) := fun i j
      =>
    Restriction.ofIsFiberedInGroupoids q hqfib (pr₁' i j ≫ q.map (f i)) U rfl with hqyrij
  -- `sφ i` is a q-fibre morphism over `q.obj (V i)`.
  have hsφ_fib : ∀ i, FibreHom q (qxr i).pt (qyr i).pt (qxr i).hpt (qyr i).hpt (sφ i) := by
    intro i
    have hqFψ : q.map (F.map (ψ i)) = eqToHom (hFpxr_qobj i) ≫ eqToHom (congrArg q.obj (hψF_cod
        i)).symm := by
      rw [hqF (ψ i), hpψ i]
      simp [eqToHom_trans]
    refine CategoryTheory.IsHomLift.of_commsq q _ (sφ i) rfl rfl ?_
    rw [hsφ]
    simp [q.map_comp, eqToHom_map, hqFψ, eqToHom_trans,
      eqToHom_refl, Category.comp_id, Category.id_comp]
  -- `sφ i` is an isomorphism.
  have hsφ_iso : ∀ i, IsIso (sφ i) := by
    intro i
    rw [hsφ]
    have := hψ_iso i
    infer_instance
  -- The family `{sφ i}` is compatible on the double overlaps: the comparison `γ i j`
  -- comes from the p-overlap compatibility of the `ψ i` pushed through `F`, and the
  -- two restriction identities from the universal property of the strongly cartesian
  -- arrows together with the pullback identification `hVijC`.
  have ed_A : ∀ i j, ∃ (γ : (qxrij i j).pt ⟶ (qyrij i j).pt),
      FibreHom q (qxrij i j).pt (qyrij i j).pt (qxrij i j).hpt (qyrij i j).hpt γ ∧
      IsRestrictionOf q (pr₁' i j) rfl rfl (qxr i) (qyr i) (qxrij i j) (qyrij i j) (sφ i) γ ∧
      IsRestrictionOf q (pr₂' i j) (hVijC i j).w (hVijC i j).w (qxr j) (qyr j)
        (qxrij i j) (qyrij i j) (sφ j) γ := by
    intro i j
    obtain ⟨xrijp, ψir, ψjr, hψir_fib, hψjr_fib, hψir_iso, hψjr_iso, hψir_r, hψjr_r, hcompat⟩ :=
      hψ_compat i j
    -- The four canonical comparison maps.
    set Aij := qxrij i j with hAij
    set Bij := qyrij i j with hBij
    set m1x := Restriction.compTo q (pr₁' i j) (q.map (f i)) rfl (qxr i) (qxrij i j) with hm1x
    set m1y := Restriction.compTo q (pr₁' i j) (q.map (f i)) rfl (qyr i) (qyrij i j) with hm1y
    set m2x := Restriction.compTo q (pr₂' i j) (q.map (f j)) (hVijC i j).w (qxr j) (qxrij i j) with
        hm2x
    set m2y := Restriction.compTo q (pr₂' i j) (q.map (f j)) (hVijC i j).w (qyr j) (qyrij i j) with
        hm2y
    -- Their factorisation properties.
    have hm1x_fac : m1x ≫ (qxr i).hom = Aij.hom :=
      Restriction.compTo_hom q (pr₁' i j) (q.map (f i)) rfl (qxr i) (qxrij i j)
    have hm1y_fac : m1y ≫ (qyr i).hom = Bij.hom :=
      Restriction.compTo_hom q (pr₁' i j) (q.map (f i)) rfl (qyr i) (qyrij i j)
    have hm2x_fac : m2x ≫ (qxr j).hom = Aij.hom :=
      Restriction.compTo_hom q (pr₂' i j) (q.map (f j)) (hVijC i j).w (qxr j) (qxrij i j)
    have hm2y_fac : m2y ≫ (qyr j).hom = Bij.hom :=
      Restriction.compTo_hom q (pr₂' i j) (q.map (f j)) (hVijC i j).w (qyr j) (qyrij i j)
    have hBcart : q.IsStronglyCartesian
        (eqToHom Bij.hpt ≫ (pr₁' i j ≫ q.map (f i)) ≫ eqToHom (rfl : q.obj U = q.obj U).symm)
            Bij.hom :=
      Bij.isCart
    set bγ : q.obj Aij.pt ⟶ q.obj Bij.pt :=
      eqToHom Aij.hpt ≫ 𝟙 (Vij' i j) ≫ eqToHom Bij.hpt.symm with hbγ
    set t : Aij.pt ⟶ U := m1x ≫ sφ i ≫ (qyr i).hom with ht
    -- The four comparison maps and `sφ` lie over the expected bases.
    have hm1x_lift : q.IsHomLift (eqToHom Aij.hpt ≫ pr₁' i j ≫ eqToHom (qxr i).hpt.symm) m1x :=
      compTo_isHomLift q (pr₁' i j) (q.map (f i)) rfl (qxr i) (qxrij i j)
    have hm1y_lift : q.IsHomLift (eqToHom Bij.hpt ≫ pr₁' i j ≫ eqToHom (qyr i).hpt.symm) m1y :=
      compTo_isHomLift q (pr₁' i j) (q.map (f i)) rfl (qyr i) (qyrij i j)
    have hm2x_lift : q.IsHomLift (eqToHom Aij.hpt ≫ pr₂' i j ≫ eqToHom (qxr j).hpt.symm) m2x :=
      compTo_isHomLift q (pr₂' i j) (q.map (f j)) (hVijC i j).w (qxr j) (qxrij i j)
    have hm2y_lift : q.IsHomLift (eqToHom Bij.hpt ≫ pr₂' i j ≫ eqToHom (qyr j).hpt.symm) m2y :=
      compTo_isHomLift q (pr₂' i j) (q.map (f j)) (hVijC i j).w (qyr j) (qyrij i j)
    have hsφ_lift : ∀ k, q.IsHomLift (eqToHom (qxr k).hpt ≫ eqToHom (qyr k).hpt.symm) (sφ k) :=
      hsφ_fib
    -- `t` lies over `bγ` composed with the base of `Bij.hom`.
    have ht_lift : q.IsHomLift
        (bγ ≫ eqToHom Bij.hpt ≫ (pr₁' i j ≫ q.map (f i)) ≫ eqToHom (rfl : q.obj U = q.obj U).symm)
            t := by
      have hyr_lift : q.IsHomLift (eqToHom (qyr i).hpt ≫ q.map (f i) ≫ eqToHom (rfl : q.obj U =
          q.obj U).symm)
          (qyr i).hom := (qyr i).isHomLift
      have hcomp1 : q.IsHomLift
          ((eqToHom (qxr i).hpt ≫ eqToHom (qyr i).hpt.symm) ≫
            (eqToHom (qyr i).hpt ≫ q.map (f i) ≫ eqToHom (rfl : q.obj U = q.obj U).symm))
          (sφ i ≫ (qyr i).hom) :=
        CategoryTheory.IsHomLift.comp q _ _ (sφ i) (qyr i).hom
      have hcomp2 : q.IsHomLift
          ((eqToHom Aij.hpt ≫ pr₁' i j ≫ eqToHom (qxr i).hpt.symm) ≫
            ((eqToHom (qxr i).hpt ≫ eqToHom (qyr i).hpt.symm) ≫
              (eqToHom (qyr i).hpt ≫ q.map (f i) ≫ eqToHom (rfl : q.obj U = q.obj U).symm)))
          (m1x ≫ sφ i ≫ (qyr i).hom) :=
        CategoryTheory.IsHomLift.comp q _ _ m1x (sφ i ≫ (qyr i).hom)
      have hbase : ((eqToHom Aij.hpt ≫ pr₁' i j ≫ eqToHom (qxr i).hpt.symm) ≫
            ((eqToHom (qxr i).hpt ≫ eqToHom (qyr i).hpt.symm) ≫
              (eqToHom (qyr i).hpt ≫ q.map (f i) ≫ eqToHom (rfl : q.obj U = q.obj U).symm)))
          = bγ ≫ eqToHom Bij.hpt ≫ (pr₁' i j ≫ q.map (f i)) ≫ eqToHom (rfl : q.obj U = q.obj
              U).symm := by
        rw [hbγ]; simp [Category.assoc, eqToHom_trans]
      rw [ht]
      rw [← hbase]; exact hcomp2
    obtain ⟨γ, ⟨hγ_lift, hγ_fac⟩, hγ_uniq⟩ := hBcart.universal_property' (φ := Bij.hom) bγ t
    -- Both restriction identities are equalities after composition with `(qyr k).hom`.
    have side : ∀ (k : I) (pk : Vij' i j ⟶ q.obj (V k)) (mx : Aij.pt ⟶ (qxr k).pt)
        (my : Bij.pt ⟶ (qyr k).pt),
        q.IsHomLift (eqToHom Aij.hpt ≫ pk ≫ eqToHom (qxr k).hpt.symm) mx →
        q.IsHomLift (eqToHom Bij.hpt ≫ pk ≫ eqToHom (qyr k).hpt.symm) my →
        my ≫ (qyr k).hom = Bij.hom → mx ≫ sφ k ≫ (qyr k).hom = t → γ ≫ my = mx ≫ sφ k := by
      intro k pk mx my _ _ hfac hx
      have hl : q.IsHomLift (eqToHom Aij.hpt ≫ pk ≫ eqToHom (qyr k).hpt.symm) (γ ≫ my) := by
        have hc : q.IsHomLift (bγ ≫ (eqToHom Bij.hpt ≫ pk ≫ eqToHom (qyr k).hpt.symm)) (γ ≫ my) :=
          CategoryTheory.IsHomLift.comp q _ _ γ my
        rwa [show bγ ≫ (eqToHom Bij.hpt ≫ pk ≫ eqToHom (qyr k).hpt.symm)
          = eqToHom Aij.hpt ≫ pk ≫ eqToHom (qyr k).hpt.symm by
            rw [hbγ]; simp [eqToHom_trans]] at hc
      have hr : q.IsHomLift (eqToHom Aij.hpt ≫ pk ≫ eqToHom (qyr k).hpt.symm) (mx ≫ sφ k) := by
        have hc : q.IsHomLift ((eqToHom Aij.hpt ≫ pk ≫ eqToHom (qxr k).hpt.symm) ≫
            (eqToHom (qxr k).hpt ≫ eqToHom (qyr k).hpt.symm)) (mx ≫ sφ k) :=
          CategoryTheory.IsHomLift.comp q _ _ mx (sφ k)
        rwa [show (eqToHom Aij.hpt ≫ pk ≫ eqToHom (qxr k).hpt.symm) ≫
            (eqToHom (qxr k).hpt ≫ eqToHom (qyr k).hpt.symm)
          = eqToHom Aij.hpt ≫ pk ≫ eqToHom (qyr k).hpt.symm by
            simp [Category.assoc, eqToHom_trans]] at hc
      have := (qyr k).isCart
      refine Functor.IsStronglyCartesian.ext (p := q)
        (f := eqToHom (qyr k).hpt ≫ q.map (f k) ≫ eqToHom (rfl : q.obj U = q.obj U).symm)
        (qyr k).hom (g := eqToHom Aij.hpt ≫ pk ≫ eqToHom (qyr k).hpt.symm) ?_
      rw [Category.assoc, Category.assoc, hfac, hγ_fac, ← hx]
    refine ⟨γ, ?_, ?_, ?_⟩
    · -- `γ` lies over the identity of the overlap.
      unfold FibreHom
      have hbe : (eqToHom Aij.hpt ≫ eqToHom Bij.hpt.symm) = bγ := by
        rw [hbγ]; simp
      rw [hbe]; exact hγ_lift
    · exact side i (pr₁' i j) m1x m1y hm1x_lift hm1y_lift hm1y_fac rfl
    · -- The `pr₂'` side.
      -- The descent compatibility: the two `U`-valued composites agree.
      have hstar : m1x ≫ sφ i ≫ (qyr i).hom = m2x ≫ sφ j ≫ (qyr j).hom := by
        -- The comparison maps in `𝒳`.
        set c1 := Restriction.compTo p (pr₁' i j) (q.map (f i)) rfl (pxr i) xrijp with hc1
        set c2 := Restriction.compTo p (pr₂' i j) (q.map (f j)) (hVijC i j).w (pxr j) xrijp with hc2
        -- `μi`, `μj`: the comparisons into `D.x i`, `D.x j`.
        set μi := Restriction.compTo p (pr₁' i j) (𝟙 (q.obj (V i))) (by simp)
          (Restriction.id p (Dp.x i) (hxp i)) (Dp.xrij i j) with hμi
        set μj := Restriction.compTo p (pr₂' i j) (𝟙 (q.obj (V j))) (by simp)
          (Restriction.id p (Dp.x j) (hxp j)) (Dp.xrji i j) with hμj
        have hp1 : c1 ≫ ψ i = ψir ≫ μi := hψir_r.symm
        have hp2 : c2 ≫ ψ j = ψjr ≫ μj := hψjr_r.symm
        have hc1_fac : c1 ≫ (pxr i).hom = xrijp.hom :=
          Restriction.compTo_hom p (pr₁' i j) (q.map (f i)) rfl (pxr i) xrijp
        have hc2_fac : c2 ≫ (pxr j).hom = xrijp.hom :=
          Restriction.compTo_hom p (pr₂' i j) (q.map (f j)) (hVijC i j).w (pxr j) xrijp
        have hFxrijp_pt : q.obj (F.obj xrijp.pt) = Vij' i j := hqFobj xrijp.hpt
        have hpxrijp_map := map_restriction_hom p _ xrijp
        have hqFxrijp_map : q.map (F.map xrijp.hom)
            = eqToHom hFxrijp_pt ≫ (pr₁' i j ≫ q.map (f i)) ≫ eqToHom hx₀q.symm := by
          rw [hqF xrijp.hom, hpxrijp_map]
          simp [eqToHom_trans]
        have hFxrijp_lift : q.IsHomLift
            (eqToHom hFxrijp_pt ≫ (pr₁' i j ≫ q.map (f i)) ≫ eqToHom hx₀q.symm) (F.map xrijp.hom)
                := by
          refine CategoryTheory.IsHomLift.of_commsq q _ _ rfl rfl ?_
          rw [hqFxrijp_map]; simp
        have hFxrijp_cart : q.IsStronglyCartesian
            (eqToHom hFxrijp_pt ≫ (pr₁' i j ≫ q.map (f i)) ≫ eqToHom hx₀q.symm) (F.map xrijp.hom)
                := by
          have h := hqcart (F.map xrijp.hom)
          rw [hqFxrijp_map] at h; exact h
        -- The comparison `eA : Aij.pt ⟶ F.obj xrijp.pt` over the identity of the overlap.
        have heA_lift : q.IsHomLift
            ((eqToHom Aij.hpt ≫ 𝟙 (Vij' i j) ≫ eqToHom hFxrijp_pt.symm) ≫
              eqToHom hFxrijp_pt ≫ (pr₁' i j ≫ q.map (f i)) ≫ eqToHom hx₀q.symm) Aij.hom := by
          have hAlift : q.IsHomLift
              (eqToHom Aij.hpt ≫ (pr₁' i j ≫ q.map (f i)) ≫ eqToHom hx₀q.symm) Aij.hom :=
                  Aij.isHomLift
          have he : ((eqToHom Aij.hpt ≫ 𝟙 (Vij' i j) ≫ eqToHom hFxrijp_pt.symm) ≫
              eqToHom hFxrijp_pt ≫ (pr₁' i j ≫ q.map (f i)) ≫ eqToHom hx₀q.symm)
              = eqToHom Aij.hpt ≫ (pr₁' i j ≫ q.map (f i)) ≫ eqToHom hx₀q.symm := by
            simp [Category.assoc, eqToHom_trans]
          rw [he]; exact hAlift
        obtain ⟨eA, ⟨heA_homlift, heA_fac⟩, heA_uniq⟩ :=
          hFxrijp_cart.universal_property' (φ := F.map xrijp.hom)
            (eqToHom Aij.hpt ≫ 𝟙 (Vij' i j) ≫ eqToHom hFxrijp_pt.symm) Aij.hom
        have hpc1_map := map_compTo p (pr₁' i j) (q.map (f i)) rfl (pxr i) xrijp
        have hpc2_map := map_compTo p (pr₂' i j) (q.map (f j)) (hVijC i j).w (pxr j) xrijp
        -- A comparison `mx` into a `q`-restriction of `F.obj x₀` factors through `eA`.
        have hmeA : ∀ (k : I) (pk : Vij' i j ⟶ q.obj (V k)) (ck : xrijp.pt ⟶ (pxr k).pt)
            (mx : Aij.pt ⟶ (qxr k).pt),
            p.map ck = eqToHom xrijp.hpt ≫ pk ≫ eqToHom (pxr k).hpt.symm →
            q.IsHomLift (eqToHom Aij.hpt ≫ pk ≫ eqToHom (qxr k).hpt.symm) mx →
            mx ≫ (qxr k).hom = Aij.hom → ck ≫ (pxr k).hom = xrijp.hom → mx = eA ≫ F.map ck := by
          intro k pk ck mx hck _ hfac hc
          have hFc : q.IsHomLift (eqToHom hFxrijp_pt ≫ pk ≫ eqToHom (qxr k).hpt.symm)
              (F.map ck) := by
            refine CategoryTheory.IsHomLift.of_commsq q _ (F.map ck) rfl rfl ?_
            rw [hqF ck, hck]
            simp [eqToHom_trans]
          have hl : q.IsHomLift (eqToHom Aij.hpt ≫ pk ≫ eqToHom (qxr k).hpt.symm)
              (eA ≫ F.map ck) := by
            have hc' : q.IsHomLift ((eqToHom Aij.hpt ≫ 𝟙 (Vij' i j) ≫ eqToHom hFxrijp_pt.symm) ≫
                (eqToHom hFxrijp_pt ≫ pk ≫ eqToHom (qxr k).hpt.symm)) (eA ≫ F.map ck) :=
              CategoryTheory.IsHomLift.comp q _ _ eA (F.map ck)
            rwa [show (eqToHom Aij.hpt ≫ 𝟙 (Vij' i j) ≫ eqToHom hFxrijp_pt.symm) ≫
                (eqToHom hFxrijp_pt ≫ pk ≫ eqToHom (qxr k).hpt.symm)
              = eqToHom Aij.hpt ≫ pk ≫ eqToHom (qxr k).hpt.symm by simp [eqToHom_trans]] at hc'
          have := (qxr k).isCart
          refine Functor.IsStronglyCartesian.ext (p := q)
            (f := eqToHom (qxr k).hpt ≫ q.map (f k) ≫ eqToHom hx₀q.symm) (qxr k).hom
            (g := eqToHom Aij.hpt ≫ pk ≫ eqToHom (qxr k).hpt.symm) ?_
          rw [hfac, Category.assoc, show (qxr k).hom = F.map (pxr k).hom from rfl,
            ← F.map_comp, hc, heA_fac]
        have hm1x_eA := hmeA i (pr₁' i j) c1 m1x hpc1_map hm1x_lift hm1x_fac hc1_fac
        have hm2x_eA := hmeA j (pr₂' i j) c2 m2x hpc2_map hm2x_lift hm2x_fac hc2_fac
        -- Reduce to an equation pre-composed with the isomorphism `eA`.
        rw [hm1x_eA, hm2x_eA]
        simp only [Category.assoc]
        refine congrArg (eA ≫ ·) ?_
        have hqyri_hom : (qyr i).hom = f i := rfl
        have hqyrj_hom : (qyr j).hom = f j := rfl
        rw [hqyri_hom, hqyrj_hom]
        have hL : F.map c1 ≫ F.map (ψ i) = F.map (ψir ≫ μi) := by rw [← F.map_comp, hp1]
        have hR : F.map c2 ≫ F.map (ψ j) = F.map (ψir ≫ Dp.φ i j ≫ μj) := by
          rw [← F.map_comp, hp2, ← hcompat, Category.assoc]
        have hμi_hom : μi = (Dp.xrij i j).hom := compTo_id_eq_hom p _ _
        have hμj_hom : μj = (Dp.xrji i j).hom := compTo_id_eq_hom p _ _
        have hFxrij : F.map ((Dp.xrij i j).hom)
            = eqToHom (D.xrij i j).hpt ≫ pr₁ i j ≫ eqToHom (D.hx i).symm :=
          map_restriction_hom F _ (D.xrij i j)
        have hFxrji : F.map ((Dp.xrji i j).hom)
            = eqToHom (D.xrji i j).hpt ≫ pr₂ i j ≫ eqToHom (D.hx j).symm :=
          map_restriction_hom F _ (D.xrji i j)
        have hFφ : F.map (D.φ i j)
            = eqToHom ((D.xrij i j).hpt.trans (D.xrji i j).hpt.symm) := by
          simpa using map_eq_of_fibreHom F (D.φ_fibreHom i j)
        rw [show F.map c1 ≫ (F.map (ψ i) ≫ eqToHom (hψF_cod i)) ≫ f i
              = (F.map c1 ≫ F.map (ψ i)) ≫ eqToHom (hψF_cod i) ≫ f i by simp [Category.assoc],
            show F.map c2 ≫ (F.map (ψ j) ≫ eqToHom (hψF_cod j)) ≫ f j
              = (F.map c2 ≫ F.map (ψ j)) ≫ eqToHom (hψF_cod j) ≫ f j by simp [Category.assoc],
            hL, hR]
        rw [show F.map (ψir ≫ μi) = F.map ψir ≫ F.map μi by rw [F.map_comp],
            show F.map (ψir ≫ Dp.φ i j ≫ μj) = F.map ψir ≫ F.map (D.φ i j) ≫ F.map μj by
              rw [F.map_comp, F.map_comp]]
        simp only [Category.assoc]
        refine congrArg (F.map ψir ≫ ·) ?_
        rw [hμi_hom, hμj_hom, hFxrij, hFxrji, hFφ]
        have hcodi : hψF_cod i = D.hx i := rfl
        have hcodj : hψF_cod j = D.hx j := rfl
        rw [hcodi, hcodj]
        have hw : pr₁ i j ≫ f i = pr₂ i j ≫ f j := (hVij i j).w
        simp only [Category.assoc, eqToHom_refl, Category.id_comp,
          eqToHom_trans_assoc]
        rw [hw]
      exact side j (pr₂' i j) m2x m2y hm2x_lift hm2y_lift hm2y_fac hstar.symm
  -- Glue `{sφ i}` into an isomorphism `s : F.obj x₀ ⟶ U` of `𝒴` over `𝟙 c₀`, then lift
  -- `inv s` through `F` to replace `x₀` by an object `x` with `F.obj x = U`, together
  -- with an isomorphism `e : x₀ ⟶ x` whose `F`-image is `s`.
  obtain ⟨x, hx_wit, e, he_iso, s, hs_fib, hs_iso, hs_restr, he_s⟩ :
      ∃ (x : 𝒳) (hx_wit : F.obj x = U) (e : x₀ ⟶ x), IsIso e ∧
        ∃ (s : F.obj x₀ ⟶ U),
          q.IsHomLift (𝟙 c₀) s ∧ IsIso s ∧
          (∀ i, (qxr i).hom ≫ s = sφ i ≫ (qyr i).hom) ∧
          F.map e = s ≫ eqToHom hx_wit.symm := by
    -- Glue `{sφ i}` using the `Isom` sheaf condition of `q`.
    have hsheaf := hq.isom_isSheaf (F.obj x₀) U hx₀q rfl
      (fun i => q.obj (V i)) (fun i => q.map (f i)) hcov𝒞
      Vij' pr₁' pr₂' hVijC qxr qyr qxrij qyrij
    obtain ⟨s, ⟨hs_fibF, hs_iso, hs_restr⟩, _⟩ := hsheaf sφ hsφ_fib hsφ_iso ed_A
    -- Convert the fibre-morphism condition into a lift of `𝟙 c₀`.
    have hs_fib : q.IsHomLift (𝟙 c₀) s := by
      refine CategoryTheory.IsHomLift.of_commsq q (𝟙 c₀) s hx₀q (rfl : q.obj U = q.obj U) ?_
      rw [map_eq_of_fibreHom q hs_fibF]; simp
    -- Lift `inv s : U ⟶ F.obj x₀` through `F` to get `c : x ⟶ x₀`.
    have := hs_iso
    obtain ⟨x, c, hc_lift⟩ := hF₂.exists_lift (CategoryTheory.inv s : U ⟶ F.obj x₀) x₀ rfl
    have := hc_lift
    have hx_wit : F.obj x = U :=
      CategoryTheory.IsHomLift.domain_eq F (CategoryTheory.inv s) c
    have hFc : F.map c = eqToHom hx_wit ≫ CategoryTheory.inv s := by
      have hfac := CategoryTheory.IsHomLift.fac F (CategoryTheory.inv s) c
      have hfac' : eqToHom hx_wit.symm ≫ F.map c = CategoryTheory.inv s := by
        simpa using hfac.symm
      rw [← hfac']
      simp
    -- `F.map c` is an isomorphism, hence so is `c`.
    have hFc_iso : IsIso (F.map c) := by rw [hFc]; infer_instance
    have hc_iso : IsIso c := isIso_of_isIso_map hF₂ c
    refine ⟨x, hx_wit, CategoryTheory.inv c, inferInstance, s, hs_fib, hs_iso, hs_restr, ?_⟩
    have hgoal : F.map (CategoryTheory.inv c) = s ≫ eqToHom hx_wit.symm := by
      rw [Functor.map_inv]
      rw [IsIso.inv_eq_of_hom_inv_id (f := F.map c) (g := s ≫ eqToHom hx_wit.symm)]
      rw [hFc]
      simp [eqToHom_trans]
    exact hgoal
  -- Assemble the witness: `x` over `U`, its `F`-restrictions `xr i`, and the fibre
  -- isomorphisms `ψ' i` obtained by transporting the `ψ i` across `e`.
  have hs_e : s = F.map e ≫ eqToHom hx_wit := by
    rw [he_s]; simp [eqToHom_trans]
  -- F-restrictions of x along f i.
  set xr : ∀ i, Restriction F (f i) x hx_wit := fun i =>
    Restriction.ofIsFiberedInGroupoids F hF₂ (f i) x hx_wit with hxr
  -- The 𝒴-base `bι i : F.obj (pxr i).pt ⟶ V i` of `ψ i`, an isomorphism.
  set bι : ∀ i, F.obj (pxr i).pt ⟶ V i := fun i => F.map (ψ i) ≫ eqToHom (D.hx i) with hbι
  have hstar : ∀ i, F.map ((pxr i).hom ≫ e) ≫ eqToHom hx_wit = bι i ≫ f i := by
    intro i
    have h := hs_restr i
    have h1 : F.map (pxr i).hom ≫ s = (F.map (ψ i) ≫ eqToHom (hψF_cod i)) ≫ f i := h
    rw [hs_e] at h1
    have hcodi : hψF_cod i = D.hx i := rfl
    rw [hcodi] at h1
    rw [hbι, F.map_comp]
    -- h1 : F.map (pxr i).hom ≫ F.map e ≫ eqToHom hx_wit = (F.map (ψ i) ≫ eqToHom (D.hx i)) ≫ f i
    simp only [Category.assoc] at h1 ⊢
    exact h1
  have hFpe : ∀ i, F.map ((pxr i).hom ≫ e) = (bι i ≫ f i) ≫ eqToHom hx_wit.symm := by
    intro i
    have h := hstar i
    rw [← h]; simp [Category.assoc, eqToHom_trans]
  -- The comparison `ζ i : (pxr i).pt ⟶ (xr i).pt`, from the universal property of the
  -- strongly cartesian `(xr i).hom`.
  have hxr_cart : ∀ i, F.IsStronglyCartesian
      (eqToHom (xr i).hpt ≫ f i ≫ eqToHom hx_wit.symm) (xr i).hom := fun i => (xr i).isCart
  -- base g'_i := bι i ≫ eqToHom (xr i).hpt.symm.
  have hpe_lift : ∀ i, F.IsHomLift
      ((bι i ≫ eqToHom (xr i).hpt.symm) ≫
        (eqToHom (xr i).hpt ≫ f i ≫ eqToHom hx_wit.symm)) ((pxr i).hom ≫ e) := by
    intro i
    refine CategoryTheory.IsHomLift.of_commsq F _ _ rfl rfl ?_
    rw [hFpe i]; simp [Category.assoc]
  have hψ_iso' : ∀ i, IsIso (ψ i) := hψ_iso
  have hbι_iso : ∀ i, IsIso (bι i) := by
    intro i; rw [hbι]; have := hψ_iso i
    infer_instance
  set ζ : ∀ i, (pxr i).pt ⟶ (xr i).pt := fun i =>
    Classical.choose ((hxr_cart i).universal_property'
      (bι i ≫ eqToHom (xr i).hpt.symm) ((pxr i).hom ≫ e)) with hζ
  have hζ_spec : ∀ i, (F.IsHomLift (bι i ≫ eqToHom (xr i).hpt.symm) (ζ i) ∧
      ζ i ≫ (xr i).hom = (pxr i).hom ≫ e) := by
    intro i
    have := Classical.choose_spec ((hxr_cart i).universal_property'
      (bι i ≫ eqToHom (xr i).hpt.symm) ((pxr i).hom ≫ e))
    exact this.1
  have hFζ : ∀ i, F.map (ζ i) = bι i ≫ eqToHom (xr i).hpt.symm := fun i => by
    have := (hζ_spec i).1
    simpa using IsHomLift.fac' F (bι i ≫ eqToHom (xr i).hpt.symm) (ζ i)
  -- `ζ i` is an isomorphism: it is F-cartesian over an isomorphism of `𝒴`.
  have hζ_iso : ∀ i, IsIso (ζ i) := by
    intro i
    have : IsIso (F.map (ζ i)) := by
      rw [hFζ i]; have := hbι_iso i; infer_instance
    exact isIso_of_isIso_map hF₂ (ζ i)
  set ψ' : ∀ i, (xr i).pt ⟶ D.x i := fun i => CategoryTheory.inv (ζ i) ≫ ψ i with hψ'
  have hFζ' : ∀ i, F.map (ζ i) = F.map (ψ i) ≫ eqToHom (D.hx i) ≫ eqToHom (xr i).hpt.symm := by
    intro i
    have := (hζ_spec i).1
    rw [hFζ i, hbι]; simp [Category.assoc]
  have hψ'_iso : ∀ i, IsIso (ψ' i) := by
    intro i; rw [hψ']
    have := hζ_iso i; have := hψ_iso i; infer_instance
  have hψ'_fib : ∀ i, FibreHom F (xr i).pt (D.x i) (xr i).hpt (D.hx i) (ψ' i) := by
    intro i
    refine CategoryTheory.IsHomLift.of_commsq F _ (ψ' i) rfl rfl ?_
    have hFψ' : F.map (ψ' i) = eqToHom (xr i).hpt ≫ eqToHom (D.hx i).symm := by
      have := hζ_iso i
      have hkey : F.map (ζ i) ≫ (eqToHom (xr i).hpt ≫ eqToHom (D.hx i).symm) = F.map (ψ i) := by
        rw [hFζ' i]; simp [Category.assoc, eqToHom_trans]
      rw [hψ', F.map_comp, ← hkey, ← Category.assoc, ← F.map_comp, IsIso.inv_hom_id, F.map_id,
        Category.id_comp]
    rw [hFψ']; simp [eqToHom_trans]
  -- Assemble.
  refine ⟨x, hx_wit, xr, ψ', hψ'_fib, hψ'_iso, ?_⟩
  intro i j
  obtain ⟨xrijp, ψir, ψjr, hψir_fib, hψjr_fib, hψir_iso, hψjr_iso, hψir_r, hψjr_r, hcompat⟩ :=
    hψ_compat i j
  -- The `F`-restriction of `x` along `pr₁ i j ≫ f i`.
  set xrij : Restriction F (pr₁ i j ≫ f i) x hx_wit :=
    Restriction.ofIsFiberedInGroupoids F hF₂ (pr₁ i j ≫ f i) x hx_wit with hxrij
  set c1 := Restriction.compTo p (pr₁' i j) (q.map (f i)) rfl (pxr i) xrijp with hc1
  have hc1_fac : c1 ≫ (pxr i).hom = xrijp.hom :=
    Restriction.compTo_hom p (pr₁' i j) (q.map (f i)) rfl (pxr i) xrijp
  set μi := Restriction.compTo p (pr₁' i j) (𝟙 (q.obj (V i))) (by simp)
    (Restriction.id p (D.x i) (hxp i)) (Dpxrij i j) with hμi
  have hμi_hom : μi = (D.xrij i j).hom := compTo_id_eq_hom p _ (Dpxrij i j)
  have hP1 : ψir ≫ (D.xrij i j).hom = c1 ≫ ψ i := by
    have := hψir_r
    -- IsRestrictionOf unfolds to ψir ≫ μi = c1 ≫ ψ i.
    have h2 : ψir ≫ μi = c1 ≫ ψ i := this
    rw [← hμi_hom]; exact h2
  have hFDxrij := map_restriction_hom F _ (D.xrij i j)
  set bξ : F.obj xrijp.pt ⟶ Vij i j := F.map ψir ≫ eqToHom (D.xrij i j).hpt with hbξ
  have hbξ_iso : IsIso bξ := by
    rw [hbξ]; have := hψir_iso
    infer_instance
  have hstarξ : F.map (xrijp.hom ≫ e) ≫ eqToHom hx_wit = bξ ≫ (pr₁ i j ≫ f i) := by
    have hxh : xrijp.hom ≫ e = c1 ≫ ((pxr i).hom ≫ e) := by
      rw [← hc1_fac]; simp [Category.assoc]
    rw [hxh, F.map_comp, Category.assoc, hFpe i]
    -- F.map c1 ≫ ((bι i ≫ f i) ≫ eqToHom hx_wit.symm) ≫ eqToHom hx_wit
    rw [Category.assoc, Category.assoc, eqToHom_trans, eqToHom_refl, Category.comp_id]
    -- F.map c1 ≫ bι i ≫ f i ; bι i = F.map (ψ i) ≫ eqToHom (D.hx i)
    rw [hbι]
    rw [show F.map c1 ≫ (F.map (ψ i) ≫ eqToHom (D.hx i)) ≫ f i
          = F.map (c1 ≫ ψ i) ≫ eqToHom (D.hx i) ≫ f i by rw [F.map_comp]; simp [Category.assoc]]
    rw [← hP1, F.map_comp, hbξ, hFDxrij]
    simp [Category.assoc]
  have hFξe : F.map (xrijp.hom ≫ e) = (bξ ≫ (pr₁ i j ≫ f i)) ≫ eqToHom hx_wit.symm := by
    rw [← hstarξ]; simp [Category.assoc, eqToHom_trans]
  have hxrij_cart : F.IsStronglyCartesian
      (eqToHom xrij.hpt ≫ (pr₁ i j ≫ f i) ≫ eqToHom hx_wit.symm) xrij.hom := xrij.isCart
  have hξ_pre : F.IsHomLift
      ((bξ ≫ eqToHom xrij.hpt.symm) ≫
        (eqToHom xrij.hpt ≫ (pr₁ i j ≫ f i) ≫ eqToHom hx_wit.symm)) (xrijp.hom ≫ e) := by
    refine CategoryTheory.IsHomLift.of_commsq F _ _ rfl rfl ?_
    rw [hFξe]; simp [Category.assoc]
  set ξ : xrijp.pt ⟶ xrij.pt :=
    Classical.choose (hxrij_cart.universal_property'
      (bξ ≫ eqToHom xrij.hpt.symm) (xrijp.hom ≫ e)) with hξ
  have hξ_spec : F.IsHomLift (bξ ≫ eqToHom xrij.hpt.symm) ξ ∧ ξ ≫ xrij.hom = xrijp.hom ≫ e := by
    have := Classical.choose_spec (hxrij_cart.universal_property'
      (bξ ≫ eqToHom xrij.hpt.symm) (xrijp.hom ≫ e))
    exact this.1
  have hFξ : F.map ξ = bξ ≫ eqToHom xrij.hpt.symm := by
    have := hξ_spec.1
    have := CategoryTheory.IsHomLift.fac F (bξ ≫ eqToHom xrij.hpt.symm) ξ
    simpa using this.symm
  have hξ_iso : IsIso ξ := by
    have : IsIso (F.map ξ) := by rw [hFξ]; have := hbξ_iso; infer_instance
    exact isIso_of_isIso_map hF₂ ξ
  -- The canonical `F`-restriction of `ψ' i` along `pr₁ i j`.
  set cF := Restriction.compTo F (pr₁ i j) (f i) rfl (xr i) xrij with hcF
  have hcF_fac : cF ≫ (xr i).hom = xrij.hom :=
    Restriction.compTo_hom F (pr₁ i j) (f i) rfl (xr i) xrij
  have hcF_lift := compTo_isHomLift F (pr₁ i j) (f i) rfl (xr i) xrij
  -- The bridge `ξ ≫ cF = c1 ≫ ζ i`, by uniqueness of q-cartesian factorisations.
  have hpψir : p.map ψir = eqToHom xrijp.hpt ≫ eqToHom (Dpxrij i j).hpt.symm :=
    map_eq_of_fibreHom p hψir_fib
  -- The bridge `ξ ≫ cFk = ck ≫ ζ k`, by uniqueness of q-cartesian factorisations.
  have hkeygen : ∀ (k : I) (pk : Vij i j ⟶ V k) (cFk : xrij.pt ⟶ (xr k).pt)
      (ck : xrijp.pt ⟶ (pxr k).pt),
      F.IsHomLift (eqToHom xrij.hpt ≫ pk ≫ eqToHom (xr k).hpt.symm) cFk →
      cFk ≫ (xr k).hom = xrij.hom → ck ≫ (pxr k).hom = xrijp.hom →
      bξ ≫ pk ≫ f k = bξ ≫ pr₁ i j ≫ f i →
      p.map ck = eqToHom xrijp.hpt ≫ q.map pk ≫ eqToHom (pxr k).hpt.symm → ξ ≫ cFk = ck ≫ ζ k := by
    intro k pk cFk ck _ hcF_fac hc_fac hw hpc
    have hlhs_post : (ξ ≫ cFk) ≫ (xr k).hom = xrijp.hom ≫ e := by
      rw [Category.assoc, hcF_fac]; exact hξ_spec.2
    have hrhs_post : (ck ≫ ζ k) ≫ (xr k).hom = xrijp.hom ≫ e := by
      rw [Category.assoc, (hζ_spec k).2, ← Category.assoc, hc_fac]
    set g0 : F.obj xrijp.pt ⟶ F.obj (xr k).pt := bξ ≫ pk ≫ eqToHom (xr k).hpt.symm with hg0
    have hFcζ : F.map (ck ≫ ζ k) = g0 := by
      refine eq_of_map_eq_of_comp_eq hqfib (F.map (xr k).hom) ?_ ?_
      · rw [hg0, hbξ]
        simp only [F.map_comp, q.map_comp, hFζ' k, eqToHom_map]
        rw [hqF ck, hpc, hqF (ψ k), hpψ k, hqF ψir, hpψir]
        simp only [eqToHom_trans, Category.assoc]
        simp
      · rw [← F.map_comp, hrhs_post, hFξe, map_restriction_hom F _ (xr k), hg0, ← hw]
        simp [Category.assoc]
    have hl : F.IsHomLift g0 (ξ ≫ cFk) := by
      have := hξ_spec.1
      have hc : F.IsHomLift ((bξ ≫ eqToHom xrij.hpt.symm) ≫
          (eqToHom xrij.hpt ≫ pk ≫ eqToHom (xr k).hpt.symm)) (ξ ≫ cFk) :=
        CategoryTheory.IsHomLift.comp F _ _ ξ cFk
      rwa [show (bξ ≫ eqToHom xrij.hpt.symm) ≫ (eqToHom xrij.hpt ≫ pk ≫ eqToHom (xr k).hpt.symm)
        = g0 by rw [hg0]; simp [Category.assoc]] at hc
    have hr : F.IsHomLift g0 (ck ≫ ζ k) := by
      refine CategoryTheory.IsHomLift.of_commsq F g0 _ rfl rfl ?_
      rw [hFcζ]; simp
    refine Functor.IsStronglyCartesian.ext (p := F)
      (eqToHom (xr k).hpt ≫ f k ≫ eqToHom hx_wit.symm) (xr k).hom (g := g0) ?_
    rw [hlhs_post, hrhs_post]
  have hkey := hkeygen i (pr₁ i j) cF c1 hcF_lift hcF_fac hc1_fac rfl
    (map_compTo p (pr₁' i j) (q.map (f i)) rfl (pxr i) xrijp)
  have hDxrij_cart : F.IsStronglyCartesian
      (eqToHom (D.xrij i j).hpt ≫ pr₁ i j ≫ eqToHom (D.hx i).symm) (D.xrij i j).hom :=
    (D.xrij i j).isCart
  have hcFψ_pre : F.IsHomLift
      ((eqToHom xrij.hpt ≫ eqToHom (D.xrij i j).hpt.symm) ≫
        (eqToHom (D.xrij i j).hpt ≫ pr₁ i j ≫ eqToHom (D.hx i).symm)) (cF ≫ ψ' i) := by
    have := hcF_lift
    have hψ'fibI : F.IsHomLift (eqToHom (xr i).hpt ≫ eqToHom (D.hx i).symm) (ψ' i) := hψ'_fib i
    have hc : F.IsHomLift
        ((eqToHom xrij.hpt ≫ pr₁ i j ≫ eqToHom (xr i).hpt.symm) ≫
          (eqToHom (xr i).hpt ≫ eqToHom (D.hx i).symm)) (cF ≫ ψ' i) :=
      CategoryTheory.IsHomLift.comp F _ _ cF (ψ' i)
    have he : ((eqToHom xrij.hpt ≫ pr₁ i j ≫ eqToHom (xr i).hpt.symm) ≫
          (eqToHom (xr i).hpt ≫ eqToHom (D.hx i).symm))
        = ((eqToHom xrij.hpt ≫ eqToHom (D.xrij i j).hpt.symm) ≫
          (eqToHom (D.xrij i j).hpt ≫ pr₁ i j ≫ eqToHom (D.hx i).symm)) := by
      simp [Category.assoc, eqToHom_trans]
    rwa [he] at hc
  set ψir' : xrij.pt ⟶ (D.xrij i j).pt :=
    Classical.choose (hDxrij_cart.universal_property'
      (eqToHom xrij.hpt ≫ eqToHom (D.xrij i j).hpt.symm) (cF ≫ ψ' i)) with hψir'
  have hψir'_spec : F.IsHomLift (eqToHom xrij.hpt ≫ eqToHom (D.xrij i j).hpt.symm) ψir' ∧
      ψir' ≫ (D.xrij i j).hom = cF ≫ ψ' i := by
    have := Classical.choose_spec (hDxrij_cart.universal_property'
      (eqToHom xrij.hpt ≫ eqToHom (D.xrij i j).hpt.symm) (cF ≫ ψ' i))
    exact this.1
  -- The bridge `ψir' = inv ξ ≫ ψir`.
  have hbridge : ψir' = CategoryTheory.inv ξ ≫ ψir := by
    have hFiξ : F.map (CategoryTheory.inv ξ ≫ ψir) = eqToHom xrij.hpt ≫ eqToHom (D.xrij i
        j).hpt.symm := by
      have := hξ_iso
      have hkey0 : F.map ξ ≫ (eqToHom xrij.hpt ≫ eqToHom (D.xrij i j).hpt.symm) = F.map ψir := by
        rw [hFξ, hbξ]; simp [Category.assoc, eqToHom_trans]
      rw [F.map_comp, ← hkey0, ← Category.assoc, ← F.map_comp, IsIso.inv_hom_id, F.map_id,
        Category.id_comp]
    have hiξ_lift : F.IsHomLift (eqToHom xrij.hpt ≫ eqToHom (D.xrij i j).hpt.symm)
        (CategoryTheory.inv ξ ≫ ψir) := by
      refine CategoryTheory.IsHomLift.of_commsq F _ _ rfl rfl ?_
      rw [hFiξ]; simp [eqToHom_trans]
    have := hψir'_spec.1
    refine Functor.IsStronglyCartesian.ext (p := F)
      (eqToHom (D.xrij i j).hpt ≫ pr₁ i j ≫ eqToHom (D.hx i).symm) (D.xrij i j).hom
      (g := eqToHom xrij.hpt ≫ eqToHom (D.xrij i j).hpt.symm) ?_
    rw [hψir'_spec.2]
    -- goal: cF ≫ ψ' i = (inv ξ ≫ ψir) ≫ (D.xrij i j).hom  (orientation from ext)
    have := hξ_iso; have := hζ_iso i
    have hkey2 : CategoryTheory.inv ξ ≫ c1 = cF ≫ CategoryTheory.inv (ζ i) := by
      rw [IsIso.inv_comp_eq, ← Category.assoc, IsIso.eq_comp_inv]; exact hkey.symm
    rw [hψ', Category.assoc, hP1]
    rw [show cF ≫ CategoryTheory.inv (ζ i) ≫ ψ i = (cF ≫ CategoryTheory.inv (ζ i)) ≫ ψ i by rw
        [Category.assoc],
        show CategoryTheory.inv ξ ≫ c1 ≫ ψ i = (CategoryTheory.inv ξ ≫ c1) ≫ ψ i by rw
            [Category.assoc], hkey2]
  set ψjr' : xrij.pt ⟶ (D.xrji i j).pt := ψir' ≫ D.φ i j with hψjr'
  -- `ψir'` is a fibre morphism for `F`, by construction.
  have hψir'_fib : FibreHom F xrij.pt (D.xrij i j).pt xrij.hpt (D.xrij i j).hpt ψir' :=
    hψir'_spec.1
  -- `ψir'` is an isomorphism: F-cartesian over an isomorphism.
  have hψir'_iso : IsIso ψir' := by
    have hFψir' := map_eq_of_fibreHom F hψir'_fib
    have : IsIso (F.map ψir') := by rw [hFψir']; infer_instance
    exact isIso_of_isIso_map hF₂ ψir'
  -- `ψjr' = ψir' ≫ D.φ i j` is a fibre morphism, as a composite of two.
  have hψjr'_fib : FibreHom F xrij.pt (D.xrji i j).pt xrij.hpt (D.xrji i j).hpt ψjr' := by
    have h1 : F.IsHomLift (eqToHom xrij.hpt ≫ eqToHom (D.xrij i j).hpt.symm) ψir' := hψir'_fib
    have h2 : F.IsHomLift (eqToHom (D.xrij i j).hpt ≫ eqToHom (D.xrji i j).hpt.symm) (D.φ i j) :=
      D.φ_fibreHom i j
    have hcomp : F.IsHomLift
        ((eqToHom xrij.hpt ≫ eqToHom (D.xrij i j).hpt.symm) ≫
          (eqToHom (D.xrij i j).hpt ≫ eqToHom (D.xrji i j).hpt.symm)) ψjr' :=
      CategoryTheory.IsHomLift.comp F _ _ ψir' (D.φ i j)
    have he : ((eqToHom xrij.hpt ≫ eqToHom (D.xrij i j).hpt.symm) ≫
        (eqToHom (D.xrij i j).hpt ≫ eqToHom (D.xrji i j).hpt.symm))
        = eqToHom xrij.hpt ≫ eqToHom (D.xrji i j).hpt.symm := by simp [eqToHom_trans]
    rwa [he] at hcomp
  have hψjr'_iso : IsIso ψjr' := by
    rw [hψjr']; have := hψir'_iso; have := D.φ_iso i j; infer_instance
  refine ⟨xrij, ψir', ψjr', hψir'_fib, hψjr'_fib, hψir'_iso, hψjr'_iso, ?_, ?_, ?_⟩
  · -- The `pr₁` side, which holds by construction of `ψir'`.
    unfold IsRestrictionOf
    rw [compTo_id_eq_hom, ← hcF]
    exact hψir'_spec.2
  · -- The `pr₂` side.
    set cF2 := Restriction.compTo F (pr₂ i j) (f j) (hVij i j).w (xr j) xrij with hcF2
    have hcF2_fac : cF2 ≫ (xr j).hom = xrij.hom :=
      Restriction.compTo_hom F (pr₂ i j) (f j) (hVij i j).w (xr j) xrij
    set c2 := Restriction.compTo p (pr₂' i j) (q.map (f j)) (hVijC i j).w (pxr j) xrijp with hc2
    have hc2_fac : c2 ≫ (pxr j).hom = xrijp.hom :=
      Restriction.compTo_hom p (pr₂' i j) (q.map (f j)) (hVijC i j).w (pxr j) xrijp
    set μj := Restriction.compTo p (pr₂' i j) (𝟙 (q.obj (V j))) (by simp)
      (Restriction.id p (D.x j) (hxp j)) (Dpxrji i j) with hμj
    have hμj_hom : μj = (D.xrji i j).hom := compTo_id_eq_hom p _ (Dpxrji i j)
    have hP2 : ψjr ≫ (D.xrji i j).hom = c2 ≫ ψ j := by
      have h2 : ψjr ≫ μj = c2 ≫ ψ j := hψjr_r
      rw [← hμj_hom]; exact h2
    have hkeyj := hkeygen j (pr₂ i j) cF2 c2 (compTo_isHomLift F (pr₂ i j) (f j) (hVij i j).w
      (xr j) xrij) hcF2_fac hc2_fac (by rw [← (hVij i j).w])
      (map_compTo p (pr₂' i j) (q.map (f j)) (hVijC i j).w (pxr j) xrijp)
    -- Conclude from `hbridge`, `hcompat`, `hP2` and `hkeyj`.
    unfold IsRestrictionOf
    rw [compTo_id_eq_hom, ← hcF2, hψjr', hbridge]
    -- ((inv ξ ≫ ψir) ≫ D.φ i j) ≫ (D.xrji i j).hom = cF2 ≫ ψ' j
    have hcomp' : ψir ≫ D.φ i j = ψjr := hcompat
    have := hξ_iso; have := hζ_iso j
    have hkeyj2 : CategoryTheory.inv ξ ≫ c2 = cF2 ≫ CategoryTheory.inv (ζ j) := by
      rw [IsIso.inv_comp_eq, ← Category.assoc, IsIso.eq_comp_inv]; exact hkeyj.symm
    rw [Category.assoc, Category.assoc, ← Category.assoc ψir, hcomp', hP2, hψ']
    rw [show cF2 ≫ CategoryTheory.inv (ζ j) ≫ ψ j = (cF2 ≫ CategoryTheory.inv (ζ j)) ≫ ψ j by rw
        [Category.assoc],
        show CategoryTheory.inv ξ ≫ c2 ≫ ψ j = (CategoryTheory.inv ξ ≫ c2) ≫ ψ j by rw
            [Category.assoc], hkeyj2]
  · -- The descent compatibility `ψir' ≫ D.φ i j = ψjr'`.
    rw [hψjr']

end CategoryTheory.Functor
