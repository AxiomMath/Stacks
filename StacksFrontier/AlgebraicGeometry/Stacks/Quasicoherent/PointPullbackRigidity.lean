module

public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.AffineQuasicoherentDirectImage
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.FppfModulesBaseChange
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PushforwardCocontinuousCartesian
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.PointPullback

/-!
# Rigidity of points with respect to quasi-coherent modules

Let `𝒳` be an algebraic stack and `x, y` points of `𝒳` over an affine scheme `Spec R`.  A 2-arrow
`a : x ≅ y` induces an isomorphism of tensor functors `f_x^* ≅ f_y^*`
(`AlgebraicGeometry.Stack.AlgebraicStacks.pointPullbackTransportIso`).  This file shows that the
2-arrow is determined by it, given an affine 1-morphism `f : 𝒰 ⟶ 𝒳` from a stack whose arrows
between affine objects are detected by a quasi-coherent module (for instance the stack of a scheme
with its structure sheaf), and whose terminal arrows `f(x₀) ⟶ y` are epimorphisms of `𝒳`.  The
module that detects the 2-arrow is the direct image `f_* M`: its sections at `y` are the sections
of `M` at the fibre product `x₀ = y ×_𝒳 𝒰`, and a 2-arrow acts on them through the arrow it
induces between the fibre products.

This is the uniqueness that makes the descent datum built from Stacks 0GRP in the proof of
Stacks 0GRQ satisfy the cocycle condition: the gluing isomorphisms over the triple overlap are
2-arrows inducing the same isomorphism of tensor functors.

## Main results

* `AlgebraicGeometry.Stack.AlgebraicStacks.map_eq_of_fppfModulesPushforward_map_eq`: restriction
  maps of a direct image along two arrows agree only if those of the module along the induced
  arrows between terminal objects do.
* `AlgebraicGeometry.Stack.AlgebraicStacks.eq_of_pointPullbackTransportIso_eq`: **rigidity**.
* `AlgebraicGeometry.Stack.AlgebraicStacks.schemeStack_hom_ext_of_structureSheaf_map_eq`: the
  structure sheaf of the stack of a scheme detects arrows into affine objects.

## References

* [Stacks Project, Tag 0GRP](https://stacks.math.columbia.edu/tag/0GRP)
* [Stacks Project, Tag 0GRQ](https://stacks.math.columbia.edu/tag/0GRQ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u w

namespace AlgebraicGeometry.Stack.AlgebraicStacks

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {𝒰 𝒳 : AlgebraicStacks.{u, w} B S hS} (f : 𝒰 ⟶ 𝒳)

/-- **Restriction in a direct image over terminal arrows.**  Let `φ₁ φ₂ : y ⟶ y'` be arrows of
`𝒳`, `t` an object of `CostructuredArrow f y` and `t'` a terminal object of
`CostructuredArrow f y'`.  If the
restriction maps of the direct image `f_* M` along `φ₁` and `φ₂` agree, then so do the restriction
maps of `M` along the two induced arrows `t.left ⟶ t'.left`. -/
theorem map_eq_of_fppfModulesPushforward_map_eq (M : Stack.fppfModules B S hS 𝒰)
    {y y' : 𝒳.val.val.obj} (φ₁ φ₂ : y ⟶ y')
    {t : CostructuredArrow (CatFiberedInGroupoids.homFunctor f.hom) y}
    {t' : CostructuredArrow (CatFiberedInGroupoids.homFunctor f.hom) y'} (ht' : IsTerminal t')
    (h : ∀ z, ((fppfModulesPushforward B S hS f).obj M).val.map φ₁.op z =
      ((fppfModulesPushforward B S hS f).obj M).val.map φ₂.op z) :
    M.val.presheaf.map (ht'.from (CostructuredArrow.mk (t.hom ≫ φ₁))).left.op =
      M.val.presheaf.map (ht'.from (CostructuredArrow.mk (t.hom ≫ φ₂))).left.op := by
  let w := CatFiberedInGroupoids.homFunctor f.hom
  let e := (fppfModulesPushforwardIsoModuleDirectImage B S hS f).app M
  let j : StructuredArrow (op y) w.op := StructuredArrow.mk (Y := op t.left) t.hom.op
  let j' : StructuredArrow (op y') w.op := StructuredArrow.mk (Y := op t'.left) t'.hom.op
  have := Stacks.SheafOfModules.isIso_ranπ_of_isTerminal w M.val.presheaf ht'
  have key : ∀ (φ : y ⟶ y') (z : ((fppfModulesPushforward B S hS f).obj M).val.obj (op y')),
      (Stacks.SheafOfModules.ranπ w.op M.val.presheaf (op y) j).hom
          (e.hom.val.app (op y) (((fppfModulesPushforward B S hS f).obj M).val.map φ.op z)) =
        M.val.presheaf.map (ht'.from (CostructuredArrow.mk (t.hom ≫ φ))).left.op
          ((Stacks.SheafOfModules.ranπ w.op M.val.presheaf (op y') j').hom
            (e.hom.val.app (op y') z)) := by
    intro φ z
    let k : t.left ⟶ t'.left := (ht'.from (CostructuredArrow.mk (t.hom ≫ φ))).left
    have hk : w.map k ≫ t'.hom = t.hom ≫ φ := CostructuredArrow.w (ht'.from _)
    rw [PresheafOfModules.naturality_apply e.hom.val φ.op z]
    have h1 := ConcreteCategory.congr_hom
      (Stacks.SheafOfModules.ranπ_map w.op M.val.presheaf φ.op j) (e.hom.val.app (op y') z)
    let g : j' ⟶ (StructuredArrow.map φ.op).obj j :=
      StructuredArrow.homMk k.op (by
        change t'.hom.op ≫ (w.map k).op = φ.op ≫ t.hom.op
        rw [← op_comp, hk, op_comp])
    have h2 := ConcreteCategory.congr_hom
      (Stacks.SheafOfModules.ranπ_naturality w.op M.val.presheaf g) (e.hom.val.app (op y') z)
    exact h1.trans h2.symm
  ext m
  obtain ⟨z, rfl⟩ : ∃ z, (Stacks.SheafOfModules.ranπ w.op M.val.presheaf (op y') j').hom
      (e.hom.val.app (op y') z) = m := by
    obtain ⟨m', rfl⟩ := ((ConcreteCategory.isIso_iff_bijective _).1
      (inferInstance : IsIso (Stacks.SheafOfModules.ranπ w.op M.val.presheaf (op y') j'))).2 m
    refine ⟨e.inv.val.app (op y') m', congrArg _ ?_⟩
    exact congrArg (fun φ => φ.val.app (op y') m') e.inv_hom_id
  exact (key φ₁ z).symm.trans ((congrArg _ (congrArg _ (h z))).trans (key φ₂ z))

/-- **Rigidity of points.**  Let `f : 𝒰 ⟶ 𝒳` be an affine 1-morphism and `M` a quasi-coherent
module on `𝒰` whose restriction maps between objects over affine schemes determine the arrows
(`hM`; for `𝒰` a scheme and `M = 𝒪` this is `Γ` being faithful on affine schemes), and suppose
that the terminal arrows `f(x₀) ⟶ y` of `f` are epimorphisms in `𝒳` (`hsep`; this holds when
`f` is a covering and `𝒳` is a prestack).  Then a 2-arrow between points over an affine scheme is
determined by the isomorphism of tensor functors it induces: if `a, b : x ≅ y` induce the same
`f_x^* ≅ f_y^*`, then `a = b`. -/
theorem eq_of_pointPullbackTransportIso_eq (hf : IsAffineHom B S hS f)
    (M : quasicoherentModules B S hS 𝒰)
    (hM : ∀ ⦃u u' : 𝒰.val.val.obj⦄ (k₁ k₂ : u ⟶ u'),
      IsAffine ((BigFppfOver.toScheme B S hS).obj (𝒰.val.val.p.obj u)) →
      IsAffine ((BigFppfOver.toScheme B S hS).obj (𝒰.val.val.p.obj u')) →
      M.obj.val.presheaf.map k₁.op = M.obj.val.presheaf.map k₂.op → k₁ = k₂)
    (hsep : ∀ ⦃y : 𝒳.val.val.obj⦄
      (t : CostructuredArrow (CatFiberedInGroupoids.homFunctor f.hom) y), IsTerminal t →
      ∀ ⦃y' : 𝒳.val.val.obj⦄ (φ₁ φ₂ : y ⟶ y'), t.hom ≫ φ₁ = t.hom ≫ φ₂ → φ₁ = φ₂)
    {R : Type u} [CommRing R] {x y : 𝒳.val.val.obj}
    (e : (BigFppfOver.toScheme B S hS).obj (𝒳.val.val.p.obj x) ≅ Spec (CommRingCat.of R))
    (ey : (BigFppfOver.toScheme B S hS).obj (𝒳.val.val.p.obj y) ≅ Spec (CommRingCat.of R))
    (a b : x ≅ y)
    (ha : (BigFppfOver.toScheme B S hS).map (𝒳.val.val.p.map a.hom) ≫ ey.hom = e.hom)
    (hb : (BigFppfOver.toScheme B S hS).map (𝒳.val.val.p.map b.hom) ≫ ey.hom = e.hom)
    (h : pointPullbackTransportIso B S hS 𝒳 e ey a ha =
      pointPullbackTransportIso B S hS 𝒳 e ey b hb) : a = b := by
  let N := (affineQuasicoherentDirectImage B S hS f hf).obj M
  have hN : ∀ z, ((fppfModulesPushforward B S hS f).obj M.obj).val.map a.inv.op z =
      ((fppfModulesPushforward B S hS f).obj M.obj).val.map b.inv.op z := fun z =>
    (pointPullbackTransportIso_hom_app_apply B S hS 𝒳 e ey a ha N z).symm.trans
      ((congrArg (fun τ : pointPullback B S hS 𝒳 x e ≅ pointPullback B S hS 𝒳 y ey =>
        (τ.hom.app N).hom z) h).trans
      (pointPullbackTransportIso_hom_app_apply B S hS 𝒳 e ey b hb N z))
  obtain ⟨t, ⟨ht⟩, hta⟩ := exists_isTerminal_costructuredArrow_of_isAffineHom B S hS f hf y
    (isAffine_point B S hS 𝒳 y ey)
  obtain ⟨t', ⟨ht'⟩, hta'⟩ := exists_isTerminal_costructuredArrow_of_isAffineHom B S hS f hf x
    (isAffine_point B S hS 𝒳 x e)
  have hk := hM _ _ hta hta'
    (map_eq_of_fppfModulesPushforward_map_eq B S hS f M.obj a.inv b.inv (t := t) ht' hN)
  have hc : t.hom ≫ a.inv = t.hom ≫ b.inv :=
    (CostructuredArrow.w (ht'.from (CostructuredArrow.mk (t.hom ≫ a.inv)))).symm.trans
      ((congrArg (fun k => (CatFiberedInGroupoids.homFunctor f.hom).map k ≫ t'.hom) hk).trans
        (CostructuredArrow.w (ht'.from (CostructuredArrow.mk (t.hom ≫ b.inv)))))
  exact Iso.ext ((Iso.inv_eq_inv a b).1 (hsep t ht a.inv b.inv hc))

section SchemeStack

/-- **Functions detect arrows into affine objects of a scheme.**  For `𝒰` the stack of a scheme
`U`, two arrows `k₁ k₂ : u ⟶ u'` of `𝒰` with `u'` over an affine scheme are equal as soon as the
restriction maps of the structure sheaf `𝒪_𝒰` along them agree. -/
theorem schemeStack_hom_ext_of_structureSheaf_map_eq (U : BigFppfOver B S hS)
    {u u' : (schemeStack.{u, w} B S hS U).val.val.obj} (k₁ k₂ : u ⟶ u')
    (hu' : IsAffine ((BigFppfOver.toScheme B S hS).obj
      ((schemeStack.{u, w} B S hS U).val.val.p.obj u')))
    (h : (SheafOfModules.unit (FibredSite.ringStructureSheafCore B S hS
        (schemeStack.{u, w} B S hS U).val.val.p
        (schemeStack.{u, w} B S hS U).val.isFiberedInGroupoids .fppf)).val.presheaf.map k₁.op =
      (SheafOfModules.unit (FibredSite.ringStructureSheafCore B S hS
        (schemeStack.{u, w} B S hS U).val.val.p
        (schemeStack.{u, w} B S hS U).val.isFiberedInGroupoids .fppf)).val.presheaf.map k₂.op) :
    k₁ = k₂ := by
  have h' : ∀ s, (Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map
      ((schemeStack.{u, w} B S hS U).val.val.p.map k₁)).op) s =
      (Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map
        ((schemeStack.{u, w} B S hS U).val.val.p.map k₂)).op) s :=
    fun s => ConcreteCategory.congr_hom h s
  have hs : (BigFppfOver.toScheme B S hS).map ((schemeStack.{u, w} B S hS U).val.val.p.map k₁) =
      (BigFppfOver.toScheme B S hS).map ((schemeStack.{u, w} B S hS U).val.val.p.map k₂) :=
    ext_of_isAffine (CommRingCat.hom_ext (RingHom.ext h'))
  exact Over.OverMorphism.ext ((BigFppfOver.toScheme B S hS).map_injective hs)

end SchemeStack

end AlgebraicGeometry.Stack.AlgebraicStacks
