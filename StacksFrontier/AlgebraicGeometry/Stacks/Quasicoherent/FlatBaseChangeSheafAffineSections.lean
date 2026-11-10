module

public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleAssociatedModuleSucc
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleAffinePushforward
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.FlatBaseChangeSheafEtaleLocality
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.SmallEtalePullbackSections
public import StacksFrontier.CategoryTheory.Adjunction.BaseChangeTransposeIso
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.FlatBaseChangeSheafSliceComparison
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.SmallEtaleAssociatedModuleBaseChange
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.RestrictScalarsBaseChange
public import StacksFrontier.CategoryTheory.Sites.SliceTopos.OverFunctorIso
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.FlatBaseChangeSheafCartesian
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.LocallyQuasicoherentEtaleLocality

/-!
# The flat base change property between affine objects, read on global sections

Let `φ : x ⟶ y` be an arrow of a category fibred in groupoids over `(Sch/S)_{fppf}`, lying over a
morphism of affine schemes `a : U ⟶ V`, and let `ℱ` be an étale sheaf of modules on `𝒳`, with
sections in `Type (u + 1)`, whose restrictions to `U_étale` and `V_étale` are quasi-coherent. The
comparison map `c_φ : a^*(ℱ|_{V_ét}) ⟶ ℱ|_{U_ét}` of Stacks 0761 is an isomorphism exactly when
the base change `Γ(U, 𝒪) ⊗_{Γ(V, 𝒪)} Γ(V, ℱ) ⟶ Γ(U, ℱ)` of its transpose on global sections is
one (`AlgebraicGeometry.Stack.isIso_restrictSheafPullbackComparison_iff_isIso_finalBaseChange`).

This is the formal criterion `CategoryTheory.Adjunction.isIso_iff_isIso_baseChangeTranspose`,
with `L ⊣ Γ` and `L' ⊣ Γ'` the associated modules of the small étale sites of `V` and `U`
(`AlgebraicGeometry.SmallEtale.sheafifiedBaseChangeAdjSucc`, whose unit is invertible and whose
counit is invertible at quasi-coherent modules), `P ⊣ P_*` the inverse and direct images along
`a_{small}`, and `ext ⊣ res` extension and restriction of scalars along `Γ(V, 𝒪) ⟶ Γ(U, 𝒪)`.

## References

* [Stacks Project, Tag 0761](https://stacks.math.columbia.edu/tag/0761)
* [Stacks Project, Tag 0762](https://stacks.math.columbia.edu/tag/0762)
* [Stacks Project, Tag 0765](https://stacks.math.columbia.edu/tag/0765)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u v w m u₂ v₂

namespace AlgebraicGeometry.Stack

variable (B : BigFppfSite.{u}) (E : BigEtaleSite.{u}) (h : E.cutoff = B.cutoff)
  (S : Scheme.{u}) (hS : B.Contains S)
  {𝒳 : Type v} [Category.{w} 𝒳] (p : 𝒳 ⥤ BigFppfOver B S hS) (hp : p.IsFiberedInGroupoids)

variable {x y : 𝒳} (φ : x ⟶ y)

/-- The final object of the small étale site of the scheme below `x` obtained by base change of
the final object below `y`. -/
noncomputable abbrev finalBaseChange :
    SmallEtale E (p.obj x).left.1 (contains_base B E h S hS p x) :=
  (smallEtaleBaseChange E (smallEtaleBaseMorphism B E h S hS p φ)).obj
    (SmallEtale.final E (p.obj y).left.1 (contains_base B E h S hS p y))

/-- The map of rings of global functions `Γ(V, 𝒪) ⟶ Γ(U, 𝒪)` below `φ`, at the final objects. -/
noncomputable abbrev finalRingMap :
    (SmallEtale.structureSheaf E (p.obj y).left.1 (contains_base B E h S hS p y)).obj.obj
        (op (SmallEtale.final E (p.obj y).left.1 (contains_base B E h S hS p y))) →+*
      (SmallEtale.structureSheaf E (p.obj x).left.1 (contains_base B E h S hS p x)).obj.obj
        (op (finalBaseChange B E h S hS p φ)) :=
  ((SmallEtale.smallEtaleStructureMapRing E (smallEtaleBaseMorphism B E h S hS p φ)).hom.app
    (op (SmallEtale.final E (p.obj y).left.1 (contains_base B E h S hS p y)))).hom

/-- Global sections of the direct image along `a_{small}` are the global sections upstairs,
read through `Γ(V, 𝒪) ⟶ Γ(U, 𝒪)`. -/
noncomputable def pushforwardFinalSectionsIso :
    SheafOfModules.pushforward.{u + 1}
        (SmallEtale.smallEtaleStructureMapRing E (smallEtaleBaseMorphism B E h S hS p φ)) ⋙
        SmallEtale.sectionsSucc (t := SmallEtale.final E (p.obj y).left.1
          (contains_base B E h S hS p y)) ≅
      SmallEtale.sectionsSucc (t := finalBaseChange B E h S hS p φ) ⋙
        ModuleCat.restrictScalars.{u + 1} (finalRingMap B E h S hS p φ) :=
  NatIso.ofComponents (fun _ => Iso.refl _) (fun _ => rfl)

/-- The final object below `x` obtained by base change is terminal. -/
noncomputable abbrev finalBaseChangeIsTerminal :
    IsTerminal (finalBaseChange B E h S hS p φ) :=
  smallEtaleBaseChange_finalIsTerminal E (smallEtaleBaseMorphism B E h S hS p φ)

/-- The scheme underlying the base-changed final object is affine when the scheme below `x` is. -/
theorem isAffine_finalBaseChange (hx : IsAffine (p.obj x).left.1) (hy : IsAffine (p.obj y).left.1) :
    IsAffine ((SmallEtale.toScheme E _ _).obj (finalBaseChange B E h S hS p φ)) := by
  have : IsAffine (E.inclusion.obj (E.obj (p.obj x).left.1 (contains_base B E h S hS p x))) := hx
  have : IsAffine (E.inclusion.obj (E.obj (p.obj y).left.1 (contains_base B E h S hS p y))) := hy
  exact SmallEtale.isAffine_toScheme_smallEtaleBaseChange E (smallEtaleBaseMorphism B E h S hS p φ)
    (SmallEtale.final E (p.obj y).left.1 (contains_base B E h S hS p y)) hy

/-- The transpose of the comparison map `c_φ` on global sections, as a map of
`Γ(V, 𝒪)`-modules `Γ(V, ℱ) ⟶ Γ(U, ℱ)`. -/
noncomputable abbrev finalSectionsTranspose
    (F : SheafOfModules.{u + 1} (ringStructureSheafCore B S hS p hp (etaleTopology B)
      (etaleTopology_le_topology B))) :
    (SmallEtale.sectionsSucc (t := SmallEtale.final E (p.obj y).left.1
        (contains_base B E h S hS p y))).obj
        ((restrictSheafToSmallEtale.{u, v, w, u + 1} B E h S hS p hp y).obj F) ⟶
      (ModuleCat.restrictScalars.{u + 1} (finalRingMap B E h S hS p φ)).obj
        ((SmallEtale.sectionsSucc (t := finalBaseChange B E h S hS p φ)).obj
          ((restrictSheafToSmallEtale.{u, v, w, u + 1} B E h S hS p hp x).obj F)) :=
  (SmallEtale.sectionsSucc (t := SmallEtale.final E (p.obj y).left.1
      (contains_base B E h S hS p y))).map
    ((sheafifiedPullbackComparisonAdjunctionUnivLE.{u, v, w, u + 1} B E h S hS p hp
      (etaleTopology B) (etaleTopology_le_topology B) φ).homEquiv _ _
        (restrictSheafPullbackComparison B E h S hS p hp φ F)) ≫
    (pushforwardFinalSectionsIso B E h S hS p φ).hom.app _

/-- **The comparison map between affine objects is invertible exactly when its base change on
global sections is.** For `φ : x ⟶ y` lying over a morphism of affine schemes and an étale sheaf
of modules `ℱ` whose restrictions below `x` and `y` are quasi-coherent, `c_φ` is an isomorphism
if and only if the base change `Γ(U, 𝒪) ⊗_{Γ(V, 𝒪)} Γ(V, ℱ) ⟶ Γ(U, ℱ)` of the transpose of
`c_φ` on global sections is. -/
theorem isIso_restrictSheafPullbackComparison_iff_isIso_finalBaseChange
    (hx : IsAffine (p.obj x).left.1) (hy : IsAffine (p.obj y).left.1)
    (F : SheafOfModules.{u + 1} (ringStructureSheafCore B S hS p hp (etaleTopology B)
      (etaleTopology_le_topology B)))
    (hFx : ((restrictSheafToSmallEtale.{u, v, w, u + 1} B E h S hS p hp
      x).obj F).IsQuasicoherentOnSite)
    (hFy : ((restrictSheafToSmallEtale.{u, v, w, u + 1} B E h S hS p hp
      y).obj F).IsQuasicoherentOnSite) :
    IsIso (restrictSheafPullbackComparison B E h S hS p hp φ F) ↔
      IsIso (((ModuleCat.extendRestrictScalarsAdj.{u + 1} (finalRingMap B E h S hS p φ)).homEquiv
        _ _).symm (finalSectionsTranspose B E h S hS p hp φ F)) := by
  let adj := SmallEtale.sheafifiedBaseChangeAdjSucc
    (SmallEtale.finalIsTerminal E (p.obj y).left.1 (contains_base B E h S hS p y))
  let adj' := SmallEtale.sheafifiedBaseChangeAdjSucc (finalBaseChangeIsTerminal B E h S hS p φ)
  have hyA : IsAffine ((SmallEtale.toScheme E _ _).obj
      (SmallEtale.final E (p.obj y).left.1 (contains_base B E h S hS p y))) := hy
  have hxA := isAffine_finalBaseChange B E h S hS p φ hx hy
  have := SmallEtale.isIso_sheafifiedBaseChangeAdjSucc_counit_app
    (SmallEtale.finalIsTerminal E (p.obj y).left.1 (contains_base B E h S hS p y)) hyA _ hFy
  have := SmallEtale.isIso_sheafifiedBaseChangeAdjSucc_counit_app
    (finalBaseChangeIsTerminal B E h S hS p φ) hxA _ hFx
  have := SmallEtale.isIso_sheafifiedBaseChangeAdjSucc_unit_app
    (finalBaseChangeIsTerminal B E h S hS p φ) hxA
    ((ModuleCat.extendScalars.{u, u, u + 1} (finalRingMap B E h S hS p φ)).obj
      ((SmallEtale.sectionsSucc (t := SmallEtale.final E (p.obj y).left.1
        (contains_base B E h S hS p y))).obj
        ((restrictSheafToSmallEtale.{u, v, w, u + 1} B E h S hS p hp y).obj F)))
  exact Adjunction.isIso_iff_isIso_baseChangeTranspose adj adj'
    (sheafifiedPullbackComparisonAdjunctionUnivLE.{u, v, w, u + 1} B E h S hS p hp (etaleTopology B)
      (etaleTopology_le_topology B) φ)
    (ModuleCat.extendRestrictScalarsAdj.{u + 1} (finalRingMap B E h S hS p φ))
    (pushforwardFinalSectionsIso B E h S hS p φ)
    (restrictSheafPullbackComparison B E h S hS p hp φ F)

/-- The transpose of `g : N ⟶ (restrictScalars s).obj N'` sends `c ⊗ₜ n` to `c • g n`. -/
private theorem _root_.ModuleCat.extendRestrictScalarsAdj_homEquiv_symm_hom_tmul {A A' : Type u}
    [CommRing A] [CommRing A'] (s : A →+* A') {N : ModuleCat.{u + 1} A}
    {N' : ModuleCat.{u + 1} A'} (g : N ⟶ (ModuleCat.restrictScalars.{u + 1} s).obj N')
    (c : A') (n : N) :
    letI : Module A A' := Module.compHom A' s
    (((ModuleCat.extendRestrictScalarsAdj.{u + 1} s).homEquiv _ _).symm g).hom
      (c ⊗ₜ[A] n : TensorProduct A A' N) = c • (show N' from g.hom n) := by
  let : Module A A' := Module.compHom A' s
  let Tg := ((ModuleCat.extendRestrictScalarsAdj.{u + 1} s).homEquiv _ _).symm g
  have hone : Tg.hom ((1 : A') ⊗ₜ[A] n : TensorProduct A A' N) = g.hom n :=
    congrArg (fun q : N ⟶ (ModuleCat.restrictScalars.{u + 1} s).obj N' => q.hom n)
      (((ModuleCat.extendRestrictScalarsAdj.{u + 1} s).homEquiv _ _).apply_symm_apply g)
  exact (congrArg (fun d => Tg.hom (d ⊗ₜ[A] n : TensorProduct A A' N)) (mul_one c).symm).trans
    ((Tg.hom.map_smul c _).trans (congrArg (fun z => c • z) hone))

/-- A map `f : N →+ P` semilinear over `α : A →+* B`, together with `β : A' →+* B'` compatible with
`s : A →+* A'` and `b : B →+* B'`, induces an additive map `A' ⊗_A N →+ B' ⊗_B P` sending `c ⊗ₜ n`
to `β c ⊗ₜ f n`. -/
private theorem _root_.ModuleCat.exists_tensorProduct_addMonoidHom {A A' B B' : Type u}
    [CommRing A] [CommRing A'] [CommRing B] [CommRing B']
    (s : A →+* A') (b : B →+* B') (α : A →+* B) (β : A' →+* B') (hsq : ∀ t, β (s t) = b (α t))
    {N : ModuleCat.{u + 1} A} {P : ModuleCat.{u + 1} B} (f : N →+ P)
    (hf : ∀ (t : A) (n : N), f (t • n) = α t • f n) :
    letI : Module A A' := Module.compHom A' s
    letI : Module B B' := Module.compHom B' b
    ∃ τ : TensorProduct A A' N →+ TensorProduct B B' P,
      ∀ (c : A') (n : N), τ (c ⊗ₜ[A] n) = β c ⊗ₜ[B] f n := by
  let : Module A A' := Module.compHom A' s
  let : Module B B' := Module.compHom B' b
  refine ⟨TensorProduct.liftAddHom
    (AddMonoidHom.mk' (fun c => AddMonoidHom.mk' (fun n => β c ⊗ₜ[B] f n)
        (fun n n' => by rw [map_add, TensorProduct.tmul_add]))
      (fun c d => AddMonoidHom.ext fun n => by
        change β (c + d) ⊗ₜ[B] f n = β c ⊗ₜ[B] f n + β d ⊗ₜ[B] f n
        rw [map_add, TensorProduct.add_tmul]))
    (fun t c n => by
      change β (s t * c) ⊗ₜ[B] f n = β c ⊗ₜ[B] f (t • n)
      rw [map_mul, hsq, hf]
      exact TensorProduct.smul_tmul (α t) (β c) (f n)), fun _ _ => rfl⟩

/-- Ring isomorphisms `α : A ≃+* B`, `β : A' ≃+* B'` compatible with `s : A →+* A'` and
`b : B →+* B'`, and an additive isomorphism `eN : N ≃+ P` semilinear over `α`, induce an additive
isomorphism `A' ⊗_A N ≃+ B' ⊗_B P` sending `c ⊗ₜ n` to `β c ⊗ₜ eN n`. -/
private theorem _root_.ModuleCat.exists_tensorProduct_addEquiv_of_ringEquiv {A A' B B' : Type u}
    [CommRing A] [CommRing A'] [CommRing B] [CommRing B']
    (s : A →+* A') (b : B →+* B') (α : A ≃+* B) (β : A' ≃+* B') (hsq : ∀ t, β (s t) = b (α t))
    {N : ModuleCat.{u + 1} A} {P : ModuleCat.{u + 1} B} (eN : N ≃+ P)
    (hN : ∀ (t : A) (n : N), eN (t • n) = α t • eN n) :
    letI : Module A A' := Module.compHom A' s
    letI : Module B B' := Module.compHom B' b
    ∃ τ : TensorProduct A A' N ≃+ TensorProduct B B' P,
      ∀ (c : A') (n : N), τ (c ⊗ₜ[A] n) = β c ⊗ₜ[B] eN n := by
  let : Module A A' := Module.compHom A' s
  let : Module B B' := Module.compHom B' b
  have hsq' : ∀ t, β.symm (b t) = s (α.symm t) := fun t =>
    β.symm_apply_eq.2 (by rw [hsq, α.apply_symm_apply])
  have hNs : ∀ (t : B) (n : P), eN.symm (t • n) = α.symm t • eN.symm n := fun t n => by
    apply eN.injective
    rw [hN, AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply, RingEquiv.apply_symm_apply]
  obtain ⟨τ, hτ⟩ := ModuleCat.exists_tensorProduct_addMonoidHom s b α β hsq eN.toAddMonoidHom hN
  obtain ⟨τ', hτ'⟩ := ModuleCat.exists_tensorProduct_addMonoidHom b s α.symm β.symm hsq'
    (P := N) eN.symm.toAddMonoidHom hNs
  have hττ' : ∀ z, τ' (τ z) = z := fun z => by
    induction z using TensorProduct.inductionOn with
    | tmul c n => rw [hτ, hτ']; simp
    | add z z' hz hz' => rw [map_add, map_add, hz, hz']
  have hτ'τ : ∀ z, τ (τ' z) = z := fun z => by
    induction z using TensorProduct.inductionOn with
    | tmul c n => rw [hτ', hτ]; simp
    | add z z' hz hz' => rw [map_add, map_add, hz, hz']
  exact ⟨AddEquiv.mk ⟨τ, τ', hττ', hτ'τ⟩ (map_add τ), hτ⟩

/-- **The base change of a semilinear map is invariant under isomorphisms of the rings and the
modules.** Given a square of commutative rings `s : A ⟶ A'`, `b : B ⟶ B'` whose vertical maps
`α`, `β` are isomorphisms, and a map `g : N ⟶ N'` over `s` identified with a map `k : P ⟶ P'`
over `b` by additive isomorphisms semilinear over `α` and `β`, the base change
`A' ⊗_A N ⟶ N'` of `g` is bijective exactly when the base change `B' ⊗_B P ⟶ P'` of `k` is. -/
theorem _root_.ModuleCat.bijective_homEquiv_symm_iff_of_ringEquiv {A A' B B' : Type u}
    [CommRing A] [CommRing A'] [CommRing B] [CommRing B']
    (s : A →+* A') (b : B →+* B') (α : A ≃+* B) (β : A' ≃+* B') (hsq : ∀ t, β (s t) = b (α t))
    {N : ModuleCat.{u + 1} A} {N' : ModuleCat.{u + 1} A'} {P : ModuleCat.{u + 1} B}
    {P' : ModuleCat.{u + 1} B'}
    (g : N ⟶ (ModuleCat.restrictScalars.{u + 1} s).obj N')
    (k : P ⟶ (ModuleCat.restrictScalars.{u + 1} b).obj P')
    (eN : N ≃+ P) (eN' : N' ≃+ P')
    (hN : ∀ (t : A) (n : N), eN (t • n) = α t • eN n)
    (hN' : ∀ (c : A') (n : N'), eN' (c • n) = β c • eN' n)
    (hg : ∀ n : N, eN' (g.hom n) = k.hom (eN n)) :
    Function.Bijective (((ModuleCat.extendRestrictScalarsAdj.{u + 1} s).homEquiv _ _).symm g).hom ↔
      Function.Bijective
        (((ModuleCat.extendRestrictScalarsAdj.{u + 1} b).homEquiv _ _).symm k).hom := by
  let : Module A A' := Module.compHom A' s
  let : Module B B' := Module.compHom B' b
  let Tg := ((ModuleCat.extendRestrictScalarsAdj.{u + 1} s).homEquiv _ _).symm g
  let Tk := ((ModuleCat.extendRestrictScalarsAdj.{u + 1} b).homEquiv _ _).symm k
  have hTg : ∀ (c : A') (n : N), Tg.hom (c ⊗ₜ[A] n : TensorProduct A A' N) =
      c • (show N' from g.hom n) := ModuleCat.extendRestrictScalarsAdj_homEquiv_symm_hom_tmul s g
  have hTk : ∀ (c : B') (n : P), Tk.hom (c ⊗ₜ[B] n : TensorProduct B B' P) =
      c • (show P' from k.hom n) := ModuleCat.extendRestrictScalarsAdj_homEquiv_symm_hom_tmul b k
  obtain ⟨τ, hτ⟩ := ModuleCat.exists_tensorProduct_addEquiv_of_ringEquiv s b α β hsq eN hN
  have hcomp : ∀ z, Tk.hom (τ z) = eN' (Tg.hom z) := fun z => by
    induction z using TensorProduct.inductionOn with
    | tmul c n =>
      refine (congrArg Tk.hom (hτ c n)).trans ((hTk (β c) (eN n)).trans ?_)
      refine Eq.trans ?_ (congrArg eN' (hTg c n)).symm
      rw [hN', hg]
    | add z z' hz hz' =>
      exact (congrArg Tk.hom (map_add τ z z')).trans ((map_add Tk.hom _ _).trans
        ((congrArg₂ (· + ·) hz hz').trans ((congrArg eN' (map_add Tg.hom z z')).trans
          (map_add eN' _ _)).symm))
  rw [← Function.Bijective.of_comp_iff' eN'.bijective,
    show (⇑eN') ∘ (⇑Tg.hom) = (⇑Tk.hom) ∘ (⇑τ) from funext fun z => (hcomp z).symm]
  exact Function.Bijective.of_comp_iff _ τ.bijective

/-- **The base-change comparison is invariant under isomorphism of arrows**, for modules with
sections in `Type (u + 1)` over a presheaf of commutative rings in `Type u`: if `g` and `g₁` are
identified by isomorphisms `α` and `β` of their sources and targets, then `M` is cartesian over
`g` exactly when it is cartesian over `g₁`. -/
theorem _root_.Stacks.PresheafOfModules.bijective_restrictionBaseChange_iff_of_arrowIso_succ
    {C : Type v} [Category.{w} C] {R : Cᵒᵖ ⥤ CommRingCat.{u}}
    (M : PresheafOfModules.{u + 1} (R ⋙ forget₂ CommRingCat RingCat))
    {X Y X₁ Y₁ : Cᵒᵖ} (g : X ⟶ Y) (g₁ : X₁ ⟶ Y₁) (α : X ⟶ X₁) (β : Y ⟶ Y₁)
    [IsIso α] [IsIso β] (hsq : g ≫ β = α ≫ g₁) :
    Function.Bijective
        (Stacks.PresheafOfModules.restrictionBaseChange.{v, w, u, u + 1} (R := R) M g).hom ↔
      Function.Bijective
        (Stacks.PresheafOfModules.restrictionBaseChange.{v, w, u, u + 1} (R := R) M g₁).hom := by
  let eM : ∀ {Z Z' : Cᵒᵖ} (γ : Z ⟶ Z') [IsIso γ], M.obj Z ≃+ M.obj Z' := fun {Z Z'} γ _ =>
    { toFun := M.map γ
      invFun := M.map (inv γ)
      left_inv := fun n => by
        rw [← PresheafOfModules.map_comp_apply, IsIso.hom_inv_id, PresheafOfModules.map_id]
        rfl
      right_inv := fun n => by
        rw [← PresheafOfModules.map_comp_apply, IsIso.inv_hom_id, PresheafOfModules.map_id]
        rfl
      map_add' := map_add _ }
  refine ModuleCat.bijective_homEquiv_symm_iff_of_ringEquiv (R.map g).hom (R.map g₁).hom
    (R.mapIso (asIso α)).commRingCatIsoToRingEquiv (R.mapIso (asIso β)).commRingCatIsoToRingEquiv
    (fun t => ?_) (M.map g) (M.map g₁) (eM α) (eM β)
    (fun t n => PresheafOfModules.map_smul M α t n) (fun t n => PresheafOfModules.map_smul M β t n)
    (fun n => ?_)
  · change (R.map β).hom ((R.map g).hom t) = (R.map g₁).hom ((R.map α).hom t)
    rw [← CommRingCat.comp_apply, ← R.map_comp, hsq, R.map_comp, CommRingCat.comp_apply]
  · change M.map β (M.map g n) = M.map g₁ (M.map α n)
    rw [← PresheafOfModules.map_comp_apply, ← PresheafOfModules.map_comp_apply, hsq]

end AlgebraicGeometry.Stack

namespace Stacks.PresheafOfModules

/-- **The base-change comparison after restriction along a functor and an isomorphism of rings**,
for modules with sections in `Type (u + 1)` over presheaves of commutative rings in `Type u`.
This is
`Stacks.PresheafOfModules.bijective_restrictionBaseChange_restrictScalars_pushforward₀_iff`
with the sections in the universe above that of the rings. -/
theorem bijective_restrictionBaseChange_restrictScalars_pushforward₀_iff_succ
    {C : Type v} [Category.{w} C] {D : Type u₂} [Category.{v₂} D]
    (q : D ⥤ C) (R : Cᵒᵖ ⥤ CommRingCat.{u}) (R' : Dᵒᵖ ⥤ CommRingCat.{u})
    (ψ : R' ⋙ forget₂ CommRingCat RingCat ⟶ q.op ⋙ R ⋙ forget₂ CommRingCat RingCat)
    (hψ : ∀ Z, IsIso (ψ.app Z))
    (M : PresheafOfModules.{u + 1} (R ⋙ forget₂ CommRingCat RingCat)) {X Y : Dᵒᵖ} (g : X ⟶ Y) :
    Function.Bijective (Stacks.PresheafOfModules.restrictionBaseChange.{u₂, v₂, u, u + 1}
      (R := R') ((_root_.PresheafOfModules.restrictScalars ψ).obj
        ((_root_.PresheafOfModules.pushforward₀ q (R ⋙ forget₂ CommRingCat RingCat)).obj M))
      g).hom ↔
    Function.Bijective (Stacks.PresheafOfModules.restrictionBaseChange.{v, w, u, u + 1} (R := R)
      M (q.op.map g)).hom := by
  have := hψ X
  have := hψ Y
  refine ModuleCat.bijective_homEquiv_symm_iff_of_ringEquiv (R'.map g).hom (R.map (q.op.map g)).hom
    (asIso (ψ.app X)).ringCatIsoToRingEquiv (asIso (ψ.app Y)).ringCatIsoToRingEquiv
    (fun t => RingHom.congr_fun (congrArg RingCat.Hom.hom (ψ.naturality g)) t)
    _ (M.map (q.op.map g)) (AddEquiv.refl _) (AddEquiv.refl _)
    (fun _ _ => rfl) (fun _ _ => rfl) (fun _ => rfl)

end Stacks.PresheafOfModules

namespace AlgebraicGeometry.Stack

variable (B : BigFppfSite.{u}) (E : BigEtaleSite.{u}) (h : E.cutoff = B.cutoff)
  (S : Scheme.{u}) (hS : B.Contains S)
  {𝒳 : Type v} [Category.{w} 𝒳] (p : 𝒳 ⥤ BigFppfOver B S hS) (hp : p.IsFiberedInGroupoids)

variable {x y : 𝒳} (φ : x ⟶ y)

/-- **The restriction of Stacks 06WJ is cartesian over a morphism `g` of the small étale site
exactly when the module is cartesian over the image of `g` under the index functor**, for modules
with sections in `Type (u + 1)`. This is
`AlgebraicGeometry.Stack.bijective_restrictionBaseChange_restrictModuleToSmallEtale_iff` one
universe up. -/
theorem bijective_restrictionBaseChange_restrictModuleToSmallEtale_iff_succ
    (G : PresheafOfModules.{u + 1}
      (ringStructureSheafCore B S hS p hp (etaleTopology B) (etaleTopology_le_topology B)).obj)
    (x : 𝒳) {T T' : SmallEtale E (p.obj x).left.1 (contains_base B E h S hS p x)}
    (g : T ⟶ T') :
    Function.Bijective (Stacks.PresheafOfModules.restrictionBaseChange.{u + 1, u, u, u + 1}
        (R := SmallEtale.commStructurePresheaf E (p.obj x).left.1 (contains_base B E h S hS p x))
        (restrictModuleToSmallEtale B E h S hS p hp x (etaleTopology B)
          (etaleTopology_le_topology B) G) g.op).hom ↔
      Function.Bijective (Stacks.PresheafOfModules.restrictionBaseChange.{v, w, u, u + 1}
        (R := (structureSheaf B S hS p hp (etaleTopology B) (etaleTopology_le_topology B)).obj)
        G ((etaleIndex B E h S hS p hp x).map g).op).hom :=
  Stacks.PresheafOfModules.bijective_restrictionBaseChange_restrictScalars_pushforward₀_iff_succ
    (etaleIndex B E h S hS p hp x)
    (structureSheaf B S hS p hp (etaleTopology B) (etaleTopology_le_topology B)).obj
    (SmallEtale.commStructurePresheaf E (p.obj x).left.1 (contains_base B E h S hS p x))
    (localStructurePresheafIso B E h S hS p hp x (etaleTopology B)
      (etaleTopology_le_topology B)).hom
    (fun Z => ((localStructurePresheafIso B E h S hS p hp x (etaleTopology B)
      (etaleTopology_le_topology B)).app Z).isIso_hom) G g.op

/-- **A module cartesian over the arrows between affine objects lying over étale morphisms is
locally quasi-coherent**, with sections in `Type (u + 1)` (Stacks 06WJ with Stacks 03DX (2) at
`u + 1`). -/
theorem isLocallyQuasicoherent_of_bijective_restrictionBaseChange_succ
    (G : SheafOfModules.{u + 1}
      (ringStructureSheafCore B S hS p hp (etaleTopology B) (etaleTopology_le_topology B)))
    (hG : ∀ ⦃x y : 𝒳⦄ (g : y ⟶ x), Etale ((BigFppfOver.toScheme B S hS).map (p.map g)) →
      IsAffine ((BigFppfOver.toScheme B S hS).obj (p.obj x)) →
      IsAffine ((BigFppfOver.toScheme B S hS).obj (p.obj y)) →
      Function.Bijective (Stacks.PresheafOfModules.restrictionBaseChange.{v, w, u, u + 1}
        (R := (structureSheaf B S hS p hp (etaleTopology B) (etaleTopology_le_topology B)).obj)
        G.val g.op).hom) :
    IsLocallyQuasicoherent B E h S hS p hp G.val :=
  ⟨G.isSheaf, fun x => ⟨restrictModuleToSmallEtale_isSheaf B E h S hS p hp x G.val G.isSheaf,
    SmallEtale.isQuasicoherentOnSite_of_isIso_restrictionBaseChange_succ E _ _
      fun {T T'} g hT hT' => (ConcreteCategory.isIso_iff_bijective _).2
        ((bijective_restrictionBaseChange_restrictModuleToSmallEtale_iff_succ B E h S hS p hp
          G.val x g).2 (hG _ (etale_etaleIndex_map B E h S hS p hp x g)
            (isAffine_etaleIndex_obj B E h S hS p hp x T' hT')
            (isAffine_etaleIndex_obj B E h S hS p hp x T hT)))⟩⟩

/-- **The base change of the transpose on global sections is the base-change comparison of `ℱ`
along the arrow of `𝒳` computing the transpose**: the base change of the transpose of `c_φ` on
global sections is bijective exactly when the base-change comparison of `ℱ` along the arrow `ξ`
of `AlgebraicGeometry.Stack.sliceComparisonLift` at the final object is. -/
theorem bijective_finalBaseChange_iff
    (F : SheafOfModules.{u + 1} (ringStructureSheafCore B S hS p hp (etaleTopology B)
      (etaleTopology_le_topology B))) :
    Function.Bijective (((ModuleCat.extendRestrictScalarsAdj.{u + 1}
        (finalRingMap B E h S hS p φ)).homEquiv _ _).symm
          (finalSectionsTranspose B E h S hS p hp φ F)) ↔
      Function.Bijective (Stacks.PresheafOfModules.restrictionBaseChange.{v, w, u, u + 1}
        (R := (structureSheaf B S hS p hp (etaleTopology B) (etaleTopology_le_topology B)).obj)
        F.val (sliceComparisonLift B E h S hS p hp φ
          (SmallEtale.final E (p.obj y).left.1 (contains_base B E h S hS p y))).left.op) := by
  let fV := SmallEtale.final E (p.obj y).left.1 (contains_base B E h S hS p y)
  let t' := finalBaseChange B E h S hS p φ
  let ξ := (sliceComparisonLift B E h S hS p hp φ fV).left
  let R := (structureSheaf B S hS p hp (etaleTopology B) (etaleTopology_le_topology B)).obj
  let Ly := localStructurePresheafIso B E h S hS p hp y (etaleTopology B)
    (etaleTopology_le_topology B)
  let Lx := localStructurePresheafIso B E h S hS p hp x (etaleTopology B)
    (etaleTopology_le_topology B)
  let s := finalRingMap B E h S hS p φ
  let ρ := restrictionPushforwardComparison B E h S hS p hp φ
    (ringStructureSheafCore B S hS p hp (etaleTopology B) (etaleTopology_le_topology B)).obj
  have hρ : ρ.app (op fV) = (ringStructureSheafCore B S hS p hp (etaleTopology B)
      (etaleTopology_le_topology B)).obj.map ξ.op :=
    restrictionPushforwardComparison_app_eq_sliceComparisonLift B E h S hS p hp φ _ fV
  have hring : ∀ t, (Lx.hom.app (op t')).hom (s t) =
      (R.map ξ.op).hom ((Ly.hom.app (op fV)).hom t) := by
    intro t
    have e2 : s t = (Lx.inv.app (op t')).hom ((ρ.app (op fV)).hom ((Ly.hom.app (op fV)).hom t)) :=
      (congrArg (fun k => (k.app (op fV)).hom t)
        (smallEtaleStructureComparison_eq_smallEtaleStructureMapRing B E h S hS p hp
          (etaleTopology B) (etaleTopology_le_topology B) φ)).symm
    rw [e2, hρ]
    exact ConcreteCategory.congr_hom (Lx.inv_hom_id_app (op t')) _
  have hg : ∀ m, (finalSectionsTranspose B E h S hS p hp φ F).hom m = (F.val.map ξ.op).hom m :=
    fun m => (sheafifiedPullbackComparisonAdjunction_homEquiv_restrictSheafPullbackComparison_app
      B E h S hS p hp φ F (op fV) m).trans (ConcreteCategory.congr_hom
        (restrictionPushforwardComparison_app_eq_sliceComparisonLift B E h S hS p hp φ
          F.val.presheaf fV) m)
  exact ModuleCat.bijective_homEquiv_symm_iff_of_ringEquiv s (R.map ξ.op).hom
    (Ly.app (op fV)).ringCatIsoToRingEquiv (Lx.app (op t')).ringCatIsoToRingEquiv hring
    (finalSectionsTranspose B E h S hS p hp φ F) (F.val.map ξ.op) (AddEquiv.refl _)
    (AddEquiv.refl _) (fun _ _ => rfl) (fun _ _ => rfl) hg

/-- An object of a slice category whose structure map is an isomorphism is terminal. -/
theorem _root_.CategoryTheory.Over.isTerminal_of_isIso_hom {C : Type*} [Category C] {X : C}
    (Y : Over X) [IsIso Y.hom] : Nonempty (IsTerminal Y) :=
  ⟨Over.mkIdTerminal.ofIso (Over.isoMk (asIso Y.hom) (by simp)).symm⟩

/-- The structure map to `z` of the object of `𝒳/z` attached to a terminal small étale object
`T` (one whose image in the slice of schemes is terminal) is an isomorphism. -/
theorem isIso_smallEtaleToSlice_hom (z : 𝒳)
    (T : SmallEtale E (p.obj z).left.1 (contains_base B E h S hS p z))
    (hT : IsTerminal ((SmallEtale.inclusion E (p.obj z).left.1
      (contains_base B E h S hS p z)).obj T)) :
    IsIso ((smallEtaleToSlice B E h S hS p hp z).obj T).hom := by
  let := isEquivalence_overPost B S hS p hp z
  have := Over.isIso_hom_of_isTerminal hT
  have : IsIso ((smallEtaleInclusion B E h (p.obj z).left.1
      (contains_base B E h S hS p z)).obj T).hom :=
    (ObjectProperty.ιOfLE (P := schemeSizeBelow E.cutoff) (P' := schemeSizeBelow B.cutoff)
      fun X hX => by simpa [h] using hX).map_isIso _
  obtain ⟨h2⟩ := Over.isTerminal_of_isIso_hom ((smallEtaleInclusion B E h (p.obj z).left.1
    (contains_base B E h S hS p z)).obj T)
  exact Over.isIso_hom_of_isTerminal
    (h2.isTerminalObj (Over.post (X := z) (p ⋙ Over.forget (B.obj hS))).inv)

/-- **Stacks 0762 between affine objects, read on sections.** For an arrow `φ : x ⟶ y` lying over
a morphism of affine schemes and an étale sheaf of modules `ℱ` (sections in `Type (u + 1)`)
whose restrictions below `x` and `y` are quasi-coherent, the comparison map `c_φ` of Stacks 0761
is an isomorphism exactly when the base-change comparison `𝒪(x) ⊗_{𝒪(y)} ℱ(y) ⟶ ℱ(x)` of the
restriction map of `ℱ` along `φ` is bijective. -/
theorem isIso_restrictSheafPullbackComparison_iff_bijective_restrictionBaseChange
    (hx : IsAffine (p.obj x).left.1) (hy : IsAffine (p.obj y).left.1)
    (F : SheafOfModules.{u + 1} (ringStructureSheafCore B S hS p hp (etaleTopology B)
      (etaleTopology_le_topology B)))
    (hFx : ((restrictSheafToSmallEtale.{u, v, w, u + 1} B E h S hS p hp
      x).obj F).IsQuasicoherentOnSite)
    (hFy : ((restrictSheafToSmallEtale.{u, v, w, u + 1} B E h S hS p hp
      y).obj F).IsQuasicoherentOnSite) :
    IsIso (restrictSheafPullbackComparison B E h S hS p hp φ F) ↔
      Function.Bijective (Stacks.PresheafOfModules.restrictionBaseChange.{v, w, u, u + 1}
        (R := (structureSheaf B S hS p hp (etaleTopology B) (etaleTopology_le_topology B)).obj)
        F.val φ.op).hom := by
  let fV := SmallEtale.final E (p.obj y).left.1 (contains_base B E h S hS p y)
  let ℓ := sliceComparisonLift B E h S hS p hp φ fV
  have hy' : IsIso ((smallEtaleToSlice B E h S hS p hp y).obj fV).hom :=
    isIso_smallEtaleToSlice_hom B E h S hS p hp y fV Over.mkIdTerminal
  have hx' : IsIso ((smallEtaleToSlice B E h S hS p hp x).obj
      (finalBaseChange B E h S hS p φ)).hom :=
    isIso_smallEtaleToSlice_hom B E h S hS p hp x _
      ((Over.mkIdTerminal : IsTerminal (Over.mk (𝟙 (E.obj (p.obj y).left.1
        (contains_base B E h S hS p y))))).isTerminalObj
        (Over.pullback (smallEtaleBaseMorphism B E h S hS p φ)) _)
  have hw : ℓ.left ≫ ((smallEtaleToSlice B E h S hS p hp y).obj fV).hom =
      ((smallEtaleToSlice B E h S hS p hp x).obj (finalBaseChange B E h S hS p φ)).hom ≫ φ :=
    Over.w ℓ
  rw [isIso_restrictSheafPullbackComparison_iff_isIso_finalBaseChange B E h S hS p hp φ hx hy F
    hFx hFy, ConcreteCategory.isIso_iff_bijective]
  refine (bijective_finalBaseChange_iff B E h S hS p hp φ F).trans ?_
  refine Stacks.PresheafOfModules.bijective_restrictionBaseChange_iff_of_arrowIso_succ
    (R := (structureSheaf B S hS p hp (etaleTopology B) (etaleTopology_le_topology B)).obj) F.val
    ℓ.left.op φ.op (inv ((smallEtaleToSlice B E h S hS p hp y).obj fV).hom).op
    (inv ((smallEtaleToSlice B E h S hS p hp x).obj (finalBaseChange B E h S hS p φ)).hom).op ?_
  rw [← op_comp, ← op_comp]
  congr 1
  rw [IsIso.eq_comp_inv, Category.assoc, hw, IsIso.inv_hom_id_assoc]

/-- **The flat base change property is checked on arrows between affine objects.** If the
comparison map `c_φ` of an étale sheaf of modules is an isomorphism at every arrow lying over a
flat morphism of affine schemes, it is an isomorphism at every arrow lying over a flat morphism. -/
theorem hasFlatBaseChangePropertySheaf_of_affine [UnivLE.{u, m}]
    (F : SheafOfModules.{m} (ringStructureSheafCore B S hS p hp (etaleTopology B)
      (etaleTopology_le_topology B)))
    (hF : ∀ {x y : 𝒳} (φ : x ⟶ y), Flat (B.inclusion.map (p.map φ).left) →
      IsAffine (p.obj x).left.1 → IsAffine (p.obj y).left.1 →
        IsIso (restrictSheafPullbackComparison B E h S hS p hp φ F)) :
    HasFlatBaseChangePropertySheafUnivLE B E h S hS p hp F := by
  intro x y φ hφ
  obtain ⟨I, z, e, hz, he, hcov, -⟩ := exists_affine_etale_ofArrows B S hS p hp y
  refine isIso_restrictSheafPullbackComparison_of_etaleCover B E h S hS p hp φ hφ e he hcov F
    fun i x' φ' hφ' => ?_
  obtain ⟨J, w, χ, hw, hχ, hcov', -⟩ := exists_affine_etale_ofArrows B S hS p hp x'
  refine isIso_of_forall_isIso_sheafifiedPullbackComparison_map B E h S hS p hp χ hχ hcov'
    (restrictSheafPullbackComparison B E h S hS p hp φ' F) fun j => ?_
  have hflat : Flat (B.inclusion.map (p.map (χ j ≫ φ')).left) := by
    rw [p.map_comp, Over.comp_left, B.inclusion.map_comp]
    have := hχ j
    infer_instance
  have := (isIso_restrictSheafPullbackComparison_comp_iff B E h S hS p hp (χ j) φ' F).2
    (hF (χ j ≫ φ') hflat (hw j) (hz i))
  have := isIso_restrictSheafPullbackComparison_of_etale B E h S hS p hp (χ j) (hχ j) F
  exact IsIso.of_isIso_comp_right _ (restrictSheafPullbackComparison B E h S hS p hp (χ j) F)

end AlgebraicGeometry.Stack

end
