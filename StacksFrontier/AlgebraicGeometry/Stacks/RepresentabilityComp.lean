module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.Algebraic.MorphismRepresentableBySpaces.Basic
public import StacksFrontier.AlgebraicGeometry.Stacks.RepresentabilityPostcomp
public import StacksFrontier.AlgebraicGeometry.Stacks.RepresentableBySpaceDescent
public import StacksFrontier.CategoryTheory.FiberedInGroupoids.Comp
public import StacksFrontier.CategoryTheory.FiberedInGroupoids.Representability.EquivalenceOverComp
public import StacksFrontier.CategoryTheory.FiberedInGroupoids.TwoFibreProduct
public import StacksFrontier.CategoryTheory.TwoFibreProduct.OverBase
public import StacksFrontier.CategoryTheory.TwoFibreProduct.OverIso

/-!
# Composition of 1-morphisms representable by algebraic spaces (Stacks 0301)

Let `S` be a scheme contained in a big fppf site `B` and let `𝒳`, `𝒴`, `𝒵` be categories fibred
in groupoids over the big fppf site of `S`. If `f : 𝒳 ⟶ 𝒴` and `g : 𝒴 ⟶ 𝒵` are 1-morphisms
representable by algebraic spaces, then so is `f ≫ g`.

## Main results

* `AlgebraicGeometry.isRepresentableByAlgebraicSpaces_comp`: a composite of 1-morphisms
  representable by algebraic spaces is representable by algebraic spaces.
* `AlgebraicGeometry.isRepresentableByAlgebraicSpaces_comp_basedFunctor`: the same for
  1-morphisms of categories over the site, with the middle category at object universe `max w₁ v`.

## References

* [Stacks Project, Tag 0300](https://stacks.math.columbia.edu/tag/0300)
* [Stacks Project, Tag 0301](https://stacks.math.columbia.edu/tag/0301)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

namespace AlgebraicGeometry

universe u v w w₁ w₃ u₁ v₁ u₂ v₂ u₃ v₃ u₄ v₄ u₅ v₅

attribute [local implicit_reducible] TwoFibreProductOver.fst
  TwoFibreProductOver.snd TwoFibreProductOver.structureFunctor

section Pullback

open TwoFibreProductOver

variable {C : Type u} [Category.{v} C]
  {A : Type u₁} [Category.{v₁} A]
  {X : Type u₂} [Category.{v₂} X]
  {Y : Type u₃} [Category.{v₃} Y]
  {Z : Type u₄} [Category.{v₄} Z]
  (pA : A ⥤ C) (pX : X ⥤ C) (pY : Y ⥤ C) (pZ : Z ⥤ C)
  (z : A ⥤ Z) (f : X ⥤ Y) (g : Y ⥤ Z) (hf : f ⋙ pY = pX)

/-- The 1-morphism `𝒰 ×_{z, 𝒵, f ⋙ g} 𝒳 ⟶ 𝒰 ×_{z, 𝒵, g} 𝒴` over `𝒞` that `f` induces on the
two base changes along one point `z` of `𝒵`, namely `(W, w, x, φ) ↦ (W, w, f x, φ)`. -/
private def pullbackMap :
    TwoFibreProductOver pA pX pZ z (f ⋙ g) ⥤ TwoFibreProductOver pA pY pZ z g where
  obj P :=
    { base := P.base, x := P.x, y := f.obj P.y, hx := P.hx
      hy := (Functor.congr_obj hf P.y).trans P.hy
      iso := P.iso, vertical := P.vertical }
  map φ :=
    { hbase := φ.hbase, a := φ.a, b := f.map φ.b, ha := φ.ha
      hb := by
        have := φ.hb
        exact Functor.isHomLift_map_of_comp_eq hf φ.hbase φ.b
      w := φ.w }
  map_id P := Hom.ext' rfl (f.map_id P.y)
  map_comp φ ψ := Hom.ext' rfl (f.map_comp φ.b ψ.b)

attribute [local implicit_reducible] pullbackMap

variable {pA pX pY pZ z f g}

/-- Verticality transported through a 1-morphism over `pA`. If `H : D ⥤ E` satisfies
`H ⋙ p = q ⋙ pA` and `φ` lies over `h` for `q`, then `H.map φ` lies over `pA.map h` for `p`. -/
private lemma mapLift
    {D : Type u₅} [Category.{v₅} D] {E : Type*} [Category E]
    {q : D ⥤ A} {p : E ⥤ C} (H : D ⥤ E) (hH : H ⋙ p = q ⋙ pA)
    {U V : A} {d e : D} (h : U ⟶ V) (φ : d ⟶ e) [q.IsHomLift h φ] :
    p.IsHomLift (pA.map h) (H.map φ) := by
  have := IsHomLift.comp_functor q pA (pA.map h) h φ
  exact Functor.isHomLift_map_of_comp_eq hH (pA.map h) φ

variable {T : Type u₅} [Category.{v₅} T] (t : T ⥤ A)
  (k : T ⥤ TwoFibreProductOver pA pY pZ z g)
  (hk : k ⋙ fst pA pY pZ z g = t)

/-- The comparison from the base change of `pullbackMap` along a point `k` of the intermediate
product `𝒰 ×_{z, 𝒵, g} 𝒴` to the base change of `f` along the point `k ⋙ π₂` of `𝒴`. On objects it
discards the intermediate datum: `(R, x, (W, w, y, ψ), ι) ↦ (pA R, x, y, π₂ ι)`. -/
private def pullbackMapFiberFunctor :
    TwoFibreProductOver t (fst pA pX pZ z (f ⋙ g)) (fst pA pY pZ z g)
      k (pullbackMap pA pX pY pZ z f g hf) ⥤
    TwoFibreProductOver (t ⋙ pA) pX pY (k ⋙ snd pA pY pZ z g) f where
  obj R := by
    have hv := R.vertical
    have hi := mapLift (pA := pA) (snd pA pY pZ z g)
      (snd_comp_eq.trans fst_comp_eq.symm) (𝟙 R.base) R.iso.hom
    change pY.IsHomLift (pA.map (𝟙 R.base)) ((snd pA pY pZ z g).map R.iso.hom) at hi
    rw [pA.map_id] at hi
    exact
      { base := pA.obj R.base, x := R.x, y := R.y.y
        hx := congrArg pA.obj R.hx
        hy := (Functor.congr_obj hf R.y.y).symm.trans
          (IsHomLift.codomain_eq pY (𝟙 (pA.obj R.base))
            ((snd pA pY pZ z g).map R.iso.hom))
        iso := (snd pA pY pZ z g).mapIso R.iso
        vertical := hi }
  map φ :=
    { hbase := pA.map φ.hbase, a := φ.a, b := φ.b.b
      ha := by
        have := φ.ha
        exact IsHomLift.comp_functor t pA (pA.map φ.hbase) φ.hbase φ.a
      hb := by
        have := φ.hb
        exact mapLift (pA := pA) (snd pA pX pZ z (f ⋙ g))
          (snd_comp_eq.trans fst_comp_eq.symm) φ.hbase φ.b
      w := by simpa [pullbackMap, snd] using congrArg Hom.b φ.w }
  map_id R := Hom.ext' rfl rfl
  map_comp φ ψ := Hom.ext' rfl rfl

attribute [local implicit_reducible] pullbackMapFiberFunctor

/-- The object of `𝒰 ×_{z, 𝒵, f ⋙ g} 𝒳` attached to an object `L` of the base change of `f`: its
`𝒰`-component is the one carried by `k L.x`, and its comparison isomorphism is that of `k L.x`
followed by the image under `g` of the comparison isomorphism of `L`. -/
private def pullbackMapFiberInverseObj
    (L : TwoFibreProductOver (t ⋙ pA) pX pY (k ⋙ snd pA pY pZ z g) f)
    (hg : g ⋙ pZ = pY) : TwoFibreProductOver pA pX pZ z (f ⋙ g) := by
  have hb : (k.obj L.x).base = L.base :=
    (k.obj L.x).hx.symm.trans
      ((congrArg pA.obj (Functor.congr_obj hk L.x)).trans L.hx)
  have hi : pZ.IsHomLift (𝟙 L.base) (k.obj L.x).iso.hom := by
    rw [← hb]
    exact (k.obj L.x).vertical
  have hL := L.vertical
  have hi' := Functor.isHomLift_map_of_comp_eq hg (𝟙 L.base) L.iso.hom
  exact
    { base := L.base, x := (k.obj L.x).x, y := L.y
      hx := (k.obj L.x).hx.trans hb, hy := L.hy
      iso := (k.obj L.x).iso ≪≫ g.mapIso L.iso
      vertical := by
        simpa using IsHomLift.comp pZ (𝟙 L.base) (𝟙 L.base)
          (k.obj L.x).iso.hom (g.map L.iso.hom) }

attribute [local implicit_reducible] pullbackMapFiberInverseObj

/-- The comparison isomorphism of the object of the base-changed product built from `L`: the
object `k L.x` of the intermediate product is isomorphic, vertically, to the image under
`pullbackMap` of `pullbackMapFiberInverseObj`. Its two components are the identity and the
comparison isomorphism of `L`. -/
private noncomputable def pullbackMapFiberIso
    (L : TwoFibreProductOver (t ⋙ pA) pX pY (k ⋙ snd pA pY pZ z g) f)
    (hg : g ⋙ pZ = pY) :
    k.obj L.x ≅ (pullbackMap pA pX pY pZ z f g hf).obj
      (pullbackMapFiberInverseObj t k hk L hg) := by
  let φ : k.obj L.x ⟶ (pullbackMap pA pX pY pZ z f g hf).obj
      (pullbackMapFiberInverseObj t k hk L hg) :=
    Hom.mk' (𝟙 _) L.iso.hom (by
      have := L.vertical
      rw [IsHomLift.fac' pY (𝟙 L.base) L.iso.hom]
      simp [pullbackMap, pullbackMapFiberInverseObj])
      (by simp [pullbackMap, pullbackMapFiberInverseObj])
  have : IsIso φ := isIso_of_isIso_components _ _ _ _ _ φ
    (by dsimp [φ]; infer_instance) (by dsimp [φ]; infer_instance)
  exact asIso φ

attribute [local implicit_reducible] pullbackMapFiberIso

/-- The functor inverse to `pullbackMapFiberFunctor`, sending an object `L` of the base change of
`f` to `(t L.x, L.x, pullbackMapFiberInverseObj L, pullbackMapFiberIso L)`. -/
private noncomputable def pullbackMapFiberInverse (hg : g ⋙ pZ = pY) :
    TwoFibreProductOver (t ⋙ pA) pX pY (k ⋙ snd pA pY pZ z g) f ⥤
    TwoFibreProductOver t (fst pA pX pZ z (f ⋙ g)) (fst pA pY pZ z g)
      k (pullbackMap pA pX pY pZ z f g hf) where
  obj L :=
    { base := t.obj L.x, x := L.x, y := pullbackMapFiberInverseObj t k hk L hg
      hx := rfl, hy := Functor.congr_obj hk L.x
      iso := pullbackMapFiberIso hf t k hk L hg
      vertical := IsHomLift.of_fac' _ _ _ (Functor.congr_obj hk L.x)
        (Functor.congr_obj hk L.x) (by simp [pullbackMapFiberIso, fst]) }
  map {L M} φ := by
    have hφ := φ.ha
    have hφ' := φ.hb
    have he : (k ⋙ fst pA pY pZ z g ⋙ pA) = t ⋙ pA := by rw [← Functor.assoc, hk]
    have hv : (fst pA pY pZ z g ⋙ pA).IsHomLift φ.hbase (k.map φ.a) :=
      Functor.isHomLift_map_of_comp_eq he φ.hbase φ.a
    have hv' : pA.IsHomLift φ.hbase ((k.map φ.a).a) :=
      IsHomLift.of_fac' pA φ.hbase _
        (IsHomLift.domain_eq (fst pA pY pZ z g ⋙ pA) φ.hbase (k.map φ.a))
        (IsHomLift.codomain_eq (fst pA pY pZ z g ⋙ pA) φ.hbase (k.map φ.a))
        (IsHomLift.fac' (fst pA pY pZ z g ⋙ pA) φ.hbase (k.map φ.a))
    refine
      { hbase := t.map φ.a, a := φ.a
        b :=
          { hbase := φ.hbase, a := (k.map φ.a).a, b := φ.b
            ha := hv', hb := φ.hb
            w := ?_ }
        ha := IsHomLift.map t φ.a
        hb := IsHomLift.of_fac' _ _ _ (Functor.congr_obj hk L.x)
          (Functor.congr_obj hk M.x) (Functor.congr_hom hk φ.a)
        w := ?_ }
    · change z.map (k.map φ.a).a ≫ ((k.obj M.x).iso.hom ≫ g.map M.iso.hom) =
        ((k.obj L.x).iso.hom ≫ g.map L.iso.hom) ≫ g.map (f.map φ.b)
      have hw : (k.map φ.a).b ≫ M.iso.hom = L.iso.hom ≫ f.map φ.b := φ.w
      rw [← Category.assoc, (k.map φ.a).w, Category.assoc, ← g.map_comp,
        hw, g.map_comp, Category.assoc]
    · apply Hom.ext'
      · simp [pullbackMapFiberIso, pullbackMap]
      · simpa [pullbackMapFiberIso, pullbackMap, pullbackMapFiberInverseObj, snd] using φ.w
  map_id L := by
    apply Hom.ext'
    · rfl
    · apply Hom.ext'
      · simp [pullbackMapFiberInverseObj]
      · rfl
  map_comp φ ψ := by
    apply Hom.ext'
    · rfl
    · apply Hom.ext'
      · simp [pullbackMapFiberInverseObj]
      · rfl

attribute [local implicit_reducible] pullbackMapFiberInverse

/-- The second component of the unit of the equivalence: for an object `R` of the base change of
`pullbackMap`, the intermediate object `R.y` is isomorphic to the one the round trip produces.
The isomorphism is built from the inverse of `π₁ R.iso` and the identity. -/
private noncomputable def pullbackMapFiberUnitSnd (hg : g ⋙ pZ = pY)
    (R : TwoFibreProductOver t (fst pA pX pZ z (f ⋙ g)) (fst pA pY pZ z g)
      k (pullbackMap pA pX pY pZ z f g hf)) :
    R.y ≅ ((pullbackMapFiberFunctor hf t k ⋙
      pullbackMapFiberInverse hf t k hk hg).obj R).y := by
  have hv := R.vertical
  have hvi := IsHomLift.lift_id_inv (fst pA pY pZ z g) R.base R.iso
  have hi := mapLift (pA := pA) (fst pA pY pZ z g) rfl (𝟙 R.base) R.iso.inv
  change pA.IsHomLift (pA.map (𝟙 R.base)) R.iso.inv.a at hi
  rw [pA.map_id] at hi
  refine TwoFibreProductOver.isoMk ((fst pA pY pZ z g).mapIso R.iso).symm (Iso.refl _) ?_ ?_
  · dsimp [pullbackMapFiberInverse, pullbackMapFiberInverseObj, pullbackMapFiberFunctor,
      pullbackMap, fst]
    rw [IsHomLift.fac' pA (𝟙 (pA.obj R.base)) R.iso.inv.a]
    simp
  · change z.map R.iso.inv.a ≫ ((k.obj R.x).iso.hom ≫ g.map R.iso.hom.b) =
      R.y.iso.hom ≫ (f ⋙ g).map (𝟙 R.y.y)
    have hw : z.map R.iso.hom.a ≫ R.y.iso.hom =
        (k.obj R.x).iso.hom ≫ g.map R.iso.hom.b := R.iso.hom.w
    rw [← hw, ← Category.assoc, ← z.map_comp]
    have hid : R.iso.inv.a ≫ R.iso.hom.a = 𝟙 _ :=
      congrArg Hom.a R.iso.inv_hom_id
    rw [hid]
    simp

attribute [local implicit_reducible] pullbackMapFiberUnitSnd

/-- The unit of the equivalence: the identity functor is isomorphic to
`pullbackMapFiberFunctor ⋙ pullbackMapFiberInverse`, componentwise by the identity on the
`𝒳`-component and `pullbackMapFiberUnitSnd` on the intermediate component. -/
private noncomputable def pullbackMapFiberUnit (hg : g ⋙ pZ = pY) :
    𝟭 _ ≅ pullbackMapFiberFunctor hf t k ⋙ pullbackMapFiberInverse hf t k hk hg :=
  NatIso.ofComponents (fun R =>
    TwoFibreProductOver.isoMk (Iso.refl _) (pullbackMapFiberUnitSnd hf t k hk hg R)
      (by
        have hv := R.vertical
        have hvi := IsHomLift.lift_id_inv (fst pA pY pZ z g) R.base R.iso
        dsimp [pullbackMapFiberUnitSnd, TwoFibreProductOver.isoMk, pullbackMapFiberInverse,
          pullbackMapFiberInverseObj, pullbackMapFiberFunctor, fst]
        have he := IsHomLift.fac' (fst pA pY pZ z g) (𝟙 R.base) R.iso.inv
        change R.iso.inv.a = _ at he
        rw [he]
        simp)
      (by
        dsimp [pullbackMapFiberInverse, pullbackMapFiberFunctor]
        apply Hom.ext'
        · simp only [CategoryTheory.Functor.map_id, Category.id_comp, comp_a]
          exact (congrArg Hom.a R.iso.hom_inv_id).symm
        · simp [pullbackMapFiberIso, pullbackMapFiberUnitSnd, TwoFibreProductOver.isoMk,
            pullbackMap]))
    (by
      intro R S φ
      apply Hom.ext'
      · simp [TwoFibreProductOver.isoMk, pullbackMapFiberFunctor, pullbackMapFiberInverse]
      · apply Hom.ext'
        · dsimp [TwoFibreProductOver.isoMk, pullbackMapFiberUnitSnd,
            pullbackMapFiberFunctor, pullbackMapFiberInverse]
          change φ.b.a ≫ S.iso.inv.a = R.iso.inv.a ≫ (k.map φ.a).a
          exact (Functor.isoWhiskerRight
            (psiIso t (fst pA pX pZ z (f ⋙ g)) (fst pA pY pZ z g) k
              (pullbackMap pA pX pY pZ z f g hf)) (fst pA pY pZ z g)).inv.naturality φ
        · simp [TwoFibreProductOver.isoMk, pullbackMapFiberUnitSnd,
            pullbackMapFiberFunctor, pullbackMapFiberInverse])

/-- The counit of the equivalence: `pullbackMapFiberInverse ⋙ pullbackMapFiberFunctor` is
isomorphic to the identity functor, componentwise by two identities. -/
private noncomputable def pullbackMapFiberCounit (hg : g ⋙ pZ = pY) :
    pullbackMapFiberInverse hf t k hk hg ⋙ pullbackMapFiberFunctor hf t k ≅ 𝟭 _ :=
  NatIso.ofComponents (fun L => TwoFibreProductOver.isoMk (Iso.refl _) (Iso.refl _)
    (by simp [pullbackMapFiberFunctor, pullbackMapFiberInverse,
      pullbackMapFiberInverseObj])
    (by simp [pullbackMapFiberFunctor, pullbackMapFiberInverse,
      pullbackMapFiberIso, snd]))
    (by intro L M φ; apply Hom.ext' <;>
      simp [TwoFibreProductOver.isoMk, pullbackMapFiberFunctor, pullbackMapFiberInverse])

/-- A fibre of the induced map between pullbacks is a fibre of the original morphism.
Both projections to the test category agree strictly. -/
private noncomputable def pullbackMapFiberEquivalence (hg : g ⋙ pZ = pY) :
    StacksRepresentableCFG.EquivalenceOver
      (fst t (fst pA pX pZ z (f ⋙ g)) (fst pA pY pZ z g)
        k (pullbackMap pA pX pY pZ z f g hf))
      (fst (t ⋙ pA) pX pY (k ⋙ snd pA pY pZ z g) f) where
  hom := ⟨pullbackMapFiberFunctor hf t k, rfl⟩
  inv := ⟨pullbackMapFiberInverse hf t k hk hg, rfl⟩
  unitIso := pullbackMapFiberUnit hf t k hk hg
  counitIso := pullbackMapFiberCounit hf t k hk hg
  unit_over := by
    ext R
    simp [pullbackMapFiberUnit, TwoFibreProductOver.isoMk, fst]
  counit_over := by
    ext L
    simp [pullbackMapFiberCounit, TwoFibreProductOver.isoMk, fst]

end Pullback


/-- The composition of two morphisms representable by algebraic spaces is
representable by algebraic spaces. -/
@[stacks 0301]
theorem isRepresentableByAlgebraicSpaces_comp
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {𝒳 𝒴 𝒵 : CatFiberedInGroupoids.{u, v, u + 1, w}
      (BigFppfOver B S hS)}
    (f : 𝒳 ⟶ 𝒴) (g : 𝒴 ⟶ 𝒵)
    (hf : IsRepresentableByAlgebraicSpaces B S hS f.hom)
    (hg : IsRepresentableByAlgebraicSpaces B S hS g.hom) :
    IsRepresentableByAlgebraicSpaces B S hS (f ≫ g).hom := by
  classical
  intro U
  dsimp only
  intro z hz
  let pU := Over.map U.hom
  let F := f.hom.toFunctor
  let G := g.hom.toFunctor
  let P := CatFiberedInGroupoids.mk
    (BasedCategory.ofFunctor (TwoFibreProductOver.fst pU 𝒳.val.p 𝒵.val.p z (F ⋙ G)))
    (Stack.fst_isFiberedInGroupoids_overMap U.hom 𝒳.val.p 𝒵.val.p z (F ⋙ G)
      𝒳.property 𝒵.property hz (by rw [Functor.assoc, g.hom.w, f.hom.w]))
  let Q := CatFiberedInGroupoids.mk
    (BasedCategory.ofFunctor (TwoFibreProductOver.fst pU 𝒴.val.p 𝒵.val.p z G))
    (Stack.fst_isFiberedInGroupoids_overMap U.hom 𝒴.val.p 𝒵.val.p z G
      𝒴.property 𝒵.property hz g.hom.w)
  let r : P ⟶ Q := Bicategory.InducedBicategory.mkHom
    { toFunctor := pullbackMap pU 𝒳.val.p 𝒴.val.p 𝒵.val.p z F G f.hom.w
      w := rfl }
  have hr : IsRepresentableByAlgebraicSpaces B U.left.1 U.left.2 r.hom := by
    intro V
    dsimp only
    intro k hk
    let t := Over.map V.hom
    let W : BigFppfOver B S hS := pU.obj V
    let y := k ⋙ TwoFibreProductOver.snd pU 𝒴.val.p 𝒵.val.p z G
    have ht : t ⋙ pU = Over.map W.hom := (Over.mapComp_eq V.hom U.hom).symm
    have hy : y ⋙ 𝒴.val.p = Over.map W.hom :=
      (congrArg (fun H => k ⋙ H)
        (TwoFibreProductOver.snd_comp_eq.trans
          TwoFibreProductOver.fst_comp_eq.symm)).trans
        ((congrArg (fun H => H ⋙ pU) hk).trans ht)
    obtain ⟨H, hH, ⟨e⟩⟩ := hf W y hy
    exact ⟨H, hH, ⟨StacksRepresentableCFG.EquivalenceOver.trans
      (pullbackMapFiberEquivalence f.hom.w t k hk g.hom.w) (ht ▸ e)⟩⟩
  exact isRepresentableByAlgebraicSpace_of_representable B U.left.1 U.left.2 P Q r hr
    (hg U z hz)

/-- The composite of two 1-morphisms of categories fibred in groupoids over the site that are
representable by algebraic spaces is representable by algebraic spaces. The source and the target
of the composite have independent object universes `w₁` and `w₃`, and the middle category has
object universe `max w₁ v`. -/
theorem isRepresentableByAlgebraicSpaces_comp_basedFunctor
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {𝒳 : CatFiberedInGroupoids.{u, v, u + 1, w₁} (BigFppfOver B S hS)}
    {𝒴 : CatFiberedInGroupoids.{u, v, u + 1, max w₁ v} (BigFppfOver B S hS)}
    {𝒵 : CatFiberedInGroupoids.{u, v, u + 1, w₃} (BigFppfOver B S hS)}
    (f : 𝒳.val ⥤ᵇ 𝒴.val) (g : 𝒴.val ⥤ᵇ 𝒵.val)
    (hf : IsRepresentableByAlgebraicSpaces B S hS f)
    (hg : IsRepresentableByAlgebraicSpaces B S hS g) :
    IsRepresentableByAlgebraicSpaces B S hS (BasedFunctor.comp f g) := by
  classical
  intro U
  dsimp only
  intro z hz
  let pU := Over.map U.hom
  let F := f.toFunctor
  let G := g.toFunctor
  let P := CatFiberedInGroupoids.mk
    (BasedCategory.ofFunctor (TwoFibreProductOver.fst pU 𝒳.val.p 𝒵.val.p z (F ⋙ G)))
    (Stack.fst_isFiberedInGroupoids_overMap U.hom 𝒳.val.p 𝒵.val.p z (F ⋙ G)
      𝒳.property 𝒵.property hz (by rw [Functor.assoc, g.w, f.w]))
  let Q := CatFiberedInGroupoids.mk
    (BasedCategory.ofFunctor (TwoFibreProductOver.fst pU 𝒴.val.p 𝒵.val.p z G))
    (Stack.fst_isFiberedInGroupoids_overMap U.hom 𝒴.val.p 𝒵.val.p z G
      𝒴.property 𝒵.property hz g.w)
  let r : P ⟶ Q := Bicategory.InducedBicategory.mkHom
    { toFunctor := pullbackMap pU 𝒳.val.p 𝒴.val.p 𝒵.val.p z F G f.w
      w := rfl }
  have hr : IsRepresentableByAlgebraicSpaces B U.left.1 U.left.2 r.hom := by
    intro V
    dsimp only
    intro k hk
    let t := Over.map V.hom
    let W : BigFppfOver B S hS := pU.obj V
    let y := k ⋙ TwoFibreProductOver.snd pU 𝒴.val.p 𝒵.val.p z G
    have ht : t ⋙ pU = Over.map W.hom := (Over.mapComp_eq V.hom U.hom).symm
    have hy : y ⋙ 𝒴.val.p = Over.map W.hom :=
      (congrArg (fun H => k ⋙ H)
        (TwoFibreProductOver.snd_comp_eq.trans
          TwoFibreProductOver.fst_comp_eq.symm)).trans
        ((congrArg (fun H => H ⋙ pU) hk).trans ht)
    obtain ⟨H, hH, ⟨e⟩⟩ := hf W y hy
    exact ⟨H, hH, ⟨StacksRepresentableCFG.EquivalenceOver.trans
      (pullbackMapFiberEquivalence f.w t k hk g.w) (ht ▸ e)⟩⟩
  exact isRepresentableByAlgebraicSpace_of_representable B U.left.1 U.left.2 P Q r hr
    (hg U z hz)

end AlgebraicGeometry

end
