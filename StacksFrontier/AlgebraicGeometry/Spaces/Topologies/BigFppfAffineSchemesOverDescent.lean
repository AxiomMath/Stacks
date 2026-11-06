module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DenseSubsiteBaseChange
public import StacksFrontier.Algebra.Category.Ring.PushoutTensorComparison
public import StacksFrontier.AlgebraicGeometry.Descent.Module.AmitsurAcyclic
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.BigFppfAffineSchemesOver
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.BigFppfRingedSite
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.GlobalFunctionsRepresentable
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.BigFppfStructureSheaf
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.BigSiteColimits.AffineFppfFaithfullyFlat
public import StacksFrontier.AlgebraicGeometry.Stacks.Sheaves.FibreProducts
public import StacksFrontier.CategoryTheory.Sites.Cohomology.ModulesOnACategory.TerminalBaseChangeDescent

/-!
# Faithfully flat descent on the affine schemes over an object of the big fppf site of a space

Let `T` be a big fppf site of algebraic spaces over a scheme `S`, `X` one of its objects and `V`
an object of `(Spaces/X)_fppf`. On the affine schemes over `V`
(`AlgebraicGeometry.BigFppfSpaceSite.AffineSchemesOver`) the sections of the structure sheaf are
the global regular functions on represented algebraic spaces, that is, up to a universe lift, the
global sections of the representing affine schemes. Hence a finite family of affine schemes over
`V` which is an fppf covering family of schemes has a faithfully flat product of rings over the
ring of the object covered, and its pairwise fibre products have the tensor products of the rings
as their rings. By faithfully flat descent of modules (Stacks 023M) the base change presheaf
`A ↦ 𝒪(A) ⊗ M` attached to a module over the ring of a terminal affine scheme over `V` is then a
sheaf for the induced topology.

## Main definitions

* `AlgebraicGeometry.Space.globalFunctionsSchemeSpaceIso`: the global regular functions on the
  algebraic space represented by a scheme are the universe lift of its global sections.

## Main results

* `AlgebraicGeometry.Space.globalFunctionsSchemeSpaceIso_naturality`: naturality in the scheme.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The global regular functions on the algebraic space represented by `W`, identified with the
universe lift of `Γ(W, 𝒪_W)` as an isomorphism of commutative rings. -/
noncomputable def globalFunctionsSchemeSpaceIso (W : BigFppfOver B S hS) :
    (globalFunctionsPresheaf B S hS).obj (op ((schemeSpaceFunctor B S hS).obj W)) ≅
      CommRingCat.of (ULift.{u + 1} ((chartPresheaf B S hS (yoneda.obj W)).obj
        (op (CostructuredArrow.mk (𝟙 (yoneda.obj W)))))) :=
  RingEquiv.toCommRingCatIso
    ((((globalFunctionsChartEquiv B S hS ((schemeSpaceFunctor B S hS).obj W)).val.trans
      (chartFunctionsYonedaEquiv B S hS W) :
        globalFunctions' B S hS ((schemeSpaceFunctor B S hS).obj W).1 ≃+*
          (chartPresheaf B S hS (yoneda.obj W)).obj
            (op (CostructuredArrow.mk (𝟙 (yoneda.obj W)))))).trans ULift.ringEquiv.symm)

/-- **Naturality**: along the morphism of represented spaces induced by a morphism of schemes
`g : V ⟶ W`, pullback of global regular functions is the universe lift of pullback of global
sections. -/
theorem globalFunctionsSchemeSpaceIso_naturality {V W : BigFppfOver B S hS} (g : V ⟶ W) :
    (globalFunctionsPresheaf B S hS).map ((schemeSpaceFunctor B S hS).map g).op ≫
        (globalFunctionsSchemeSpaceIso B S hS V).hom =
      (globalFunctionsSchemeSpaceIso B S hS W).hom ≫
        CommRingCat.ofHom ((Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map g).op).hom.ulift) := by
  ext s
  show chartFunctionsYonedaEquiv B S hS V
      ((globalFunctionsChartEquiv B S hS ((schemeSpaceFunctor B S hS).obj V)).val
        (globalFunctionsMap B S hS ((schemeSpaceFunctor B S hS).map g) s)) =
    (chartPresheaf B S hS (yoneda.obj W)).map
      (CostructuredArrow.homMk (S := yoneda) (T := yoneda.obj W)
        (f := CostructuredArrow.mk (𝟙 (yoneda.obj V) ≫ yoneda.map g))
        (f' := CostructuredArrow.mk (𝟙 (yoneda.obj W))) g (by simp)).op
      (chartFunctionsYonedaEquiv B S hS W
        ((globalFunctionsChartEquiv B S hS ((schemeSpaceFunctor B S hS).obj W)).val s))
  exact (congrArg (chartFunctionsYonedaEquiv B S hS V)
    (globalFunctionsMap_chart B S hS ((schemeSpaceFunctor B S hS).map g) s)).trans
      (chartFunctionsYonedaEquiv_map B S hS g _)

end AlgebraicGeometry.Space

namespace AlgebraicGeometry.BigFppfSpaceSite.AffineSchemesOver

variable {S : Scheme.{u}} {T : BigFppfSpaceSite S} {X : T.Spaces} {V : BigFppfSpaceOver T X}

/-- The structure sheaf of rings of the big fppf site of `X`, restricted to the slice at `V`. -/
noncomputable abbrev sliceRingSheaf :
    Sheaf ((BigFppfSpaceOver.topology T X).over V) RingCat.{u + 1} :=
  (bigFppfRingSheaf T X).over V

/-- The structure sheaf of rings restricted to the affine schemes over `V`. -/
noncomputable abbrev ringPresheaf : (AffineSchemesOver T V)ᵒᵖ ⥤ RingCat.{u + 1} :=
  (Stacks.DenseSubsiteModules.ringRestriction (topology (T := T) (V := V))
    ((BigFppfSpaceOver.topology T X).over V) (toSlice T V) sliceRingSheaf).obj

/-- The sections of `ringPresheaf` are commutative rings. -/
instance ringPresheaf_commSections :
    Stacks.TerminalBaseChange.CommSections (ringPresheaf (T := T) (V := V)) where
  mul_comm A a b := mul_comm (G := Space.globalFunctions' T.schemeSite S T.scheme_mem
    ((schemeSpaceFunctor T.schemeSite S T.scheme_mem).obj A.unop.obj.left).1) a b

/-- The ring of an affine scheme over `V`, identified with the universe lift of the global
sections of the scheme. -/
noncomputable def ringIso (A : AffineSchemesOver T V) :
    CommRingCat.of ((ringPresheaf (T := T) (V := V)).obj (op A)) ≅
      CommRingCat.of (ULift.{u + 1}
        Γ((BigFppfOver.toScheme T.schemeSite S T.scheme_mem).obj A.obj.left, ⊤)) :=
  Space.globalFunctionsSchemeSpaceIso T.schemeSite S T.scheme_mem A.obj.left ≪≫ Iso.refl _

/-- The ring map of the structure sheaf along `homOfScheme`, read through `ringIso`, is the
universe lift of pullback of global sections. -/
lemma ringIso_naturality (W : AffineSchemesOver T V) {Z : T.Schemes}
    (hZ : IsAffine ((BigFppfOver.toScheme T.schemeSite S T.scheme_mem).obj Z))
    (φ : Z ⟶ W.obj.left) (a : (ringPresheaf (T := T) (V := V)).obj (op W)) :
    (ringIso _).hom ((ringPresheaf (T := T) (V := V)).map (homOfScheme W hZ φ).op a) =
      ULift.up (Scheme.Γ.map ((BigFppfOver.toScheme T.schemeSite S T.scheme_mem).map φ).op
        ((ringIso W).hom a).down) :=
  congrArg (fun m => m.hom a)
    (Space.globalFunctionsSchemeSpaceIso_naturality T.schemeSite S T.scheme_mem φ)

/-- **Naturality of `ringIso` along an arbitrary morphism of affine schemes over `V`**: the
restriction map of the structure sheaf is the universe lift of pullback of global sections along
the underlying morphism of schemes. -/
lemma ringIso_hom_naturality {A A' : AffineSchemesOver T V} (f : A ⟶ A') :
    CommRingCat.ofHom ((ringPresheaf (T := T) (V := V)).map f.op).hom ≫ (ringIso A).hom =
      (ringIso A').hom ≫ CommRingCat.ofHom
        ((Scheme.Γ.map
          ((BigFppfOver.toScheme T.schemeSite S T.scheme_mem).map f.hom.left).op).hom.ulift) :=
  Space.globalFunctionsSchemeSpaceIso_naturality T.schemeSite S T.scheme_mem f.hom.left

/-- The scheme underlying an affine scheme over `V` is affine. -/
private instance isAffine_toScheme_obj_left (A : AffineSchemesOver T V) :
    IsAffine ((BigFppfOver.toScheme T.schemeSite S T.scheme_mem).obj A.obj.left) :=
  A.property

attribute [local instance] ULift.algebra' in
/-- **The product of the rings of a finite family of affine schemes over `V` whose underlying
morphisms of schemes form an fppf covering is faithfully flat over the ring of the target.** -/
theorem faithfullyFlat_pi_of_fppf (W : AffineSchemesOver T V) {ι : Type} [Finite ι]
    (A : ι → AffineSchemesOver T V) (f : ∀ i, A i ⟶ W)
    (hfppf : Presieve.ofArrows
        (fun i => (BigFppfOver.toScheme T.schemeSite S T.scheme_mem).obj (A i).obj.left)
        (fun i => (BigFppfOver.toScheme T.schemeSite S T.scheme_mem).map (f i).hom.left) ∈
      Scheme.fppfPrecoverage ((BigFppfOver.toScheme T.schemeSite S T.scheme_mem).obj W.obj.left)) :
    letI : ∀ i, Algebra ((ringPresheaf (T := T) (V := V)).obj (op W))
        ((ringPresheaf (T := T) (V := V)).obj (op (A i))) :=
      fun i => ((ringPresheaf (T := T) (V := V)).map (f i).op).hom.toAlgebra
    Module.FaithfullyFlat ((ringPresheaf (T := T) (V := V)).obj (op W))
      (∀ i, (ringPresheaf (T := T) (V := V)).obj (op (A i))) := by
  let algY : ∀ i, Algebra ((ringPresheaf (T := T) (V := V)).obj (op W))
      ((ringPresheaf (T := T) (V := V)).obj (op (A i))) :=
    fun i => ((ringPresheaf (T := T) (V := V)).map (f i).op).hom.toAlgebra
  let G := BigFppfOver.toScheme T.schemeSite S T.scheme_mem
  let algΓ : ∀ i, Algebra Γ(G.obj W.obj.left, ⊤) Γ(G.obj (A i).obj.left, ⊤) :=
    fun i => (G.map (f i).hom.left).appTop.hom.toAlgebra
  have h0 : Module.FaithfullyFlat Γ(G.obj W.obj.left, ⊤) (∀ i, Γ(G.obj (A i).obj.left, ⊤)) :=
    faithfullyFlat_pi_gamma_of_ofArrows_mem_fppfPrecoverage (fun i => G.map (f i).hom.left) hfppf
      (fun _ => rfl)
  let : Algebra (ULift.{u + 1} Γ(G.obj W.obj.left, ⊤))
      (ULift.{u + 1} (∀ i, Γ(G.obj (A i).obj.left, ⊤))) :=
    ULift.algebra' _ _
  have h1 : Module.FaithfullyFlat (ULift.{u + 1} Γ(G.obj W.obj.left, ⊤))
      (ULift.{u + 1} (∀ i, Γ(G.obj (A i).obj.left, ⊤))) := by
    let R := Γ(G.obj W.obj.left, ⊤)
    let B := ∀ i, Γ(G.obj (A i).obj.left, ⊤)
    have : Module.FaithfullyFlat (ULift.{u + 1} R) R :=
      Module.FaithfullyFlat.of_linearEquiv (ULift.{u + 1} R) (ULift.{u + 1} R)
        { toFun := ULift.up, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl,
          invFun := ULift.down, left_inv := fun _ => rfl, right_inv := fun _ => rfl }
    have : Module.FaithfullyFlat R (ULift.{u + 1} B) :=
      Module.FaithfullyFlat.of_linearEquiv R B ULift.moduleEquiv
    have : IsScalarTower (ULift.{u + 1} R) R (ULift.{u + 1} B) :=
      ⟨fun x y z => ULift.ext (mul_smul x.down y z.down)⟩
    exact Module.FaithfullyFlat.trans (ULift.{u + 1} R) R (ULift.{u + 1} B)
  have h2 := (RingHom.faithfullyFlat_algebraMap_iff).2 h1
  let eW : (ringPresheaf (T := T) (V := V)).obj (op W) ≃+* ULift.{u + 1} Γ(G.obj W.obj.left, ⊤) :=
    (ringIso W).commRingCatIsoToRingEquiv
  let eY : ULift.{u + 1} (∀ i, Γ(G.obj (A i).obj.left, ⊤)) ≃+*
      ∀ i, (ringPresheaf (T := T) (V := V)).obj (op (A i)) :=
    ULift.ringEquiv.trans (RingEquiv.piCongrRight fun i =>
      ((ULift.ringEquiv : ULift.{u + 1} Γ(G.obj (A i).obj.left, ⊤) ≃+*
        Γ(G.obj (A i).obj.left, ⊤)).symm).trans (ringIso (A i)).commRingCatIsoToRingEquiv.symm)
  have h3 := RingHom.FaithfullyFlat.respectsIso.1 _ eY
    (RingHom.FaithfullyFlat.respectsIso.2 _ eW h2)
  refine (RingHom.faithfullyFlat_algebraMap_iff
    (R := (ringPresheaf (T := T) (V := V)).obj (op W))
    (S := ∀ i, (ringPresheaf (T := T) (V := V)).obj (op (A i)))).1 ?_
  convert h3 using 1
  ext a i
  exact (RingEquiv.eq_symm_apply (ringIso (A i)).commRingCatIsoToRingEquiv).2
    (congrArg (fun m => m.hom a) (ringIso_hom_naturality (f i)))

/-- **The product of the rings of a finite fppf family of affine schemes over `V` is faithfully
flat over the ring of the object covered**, for a family given by morphisms of schemes into an
affine scheme over `V`. -/
theorem faithfullyFlat_pi (W : AffineSchemesOver T V) {n : ℕ} (Z : Fin n → T.Schemes)
    (hZ : ∀ i, IsAffine ((BigFppfOver.toScheme T.schemeSite S T.scheme_mem).obj (Z i)))
    (φ : ∀ i, Z i ⟶ W.obj.left)
    (hfppf : Presieve.ofArrows
        (fun i => (BigFppfOver.toScheme T.schemeSite S T.scheme_mem).obj (Z i))
        (fun i => (BigFppfOver.toScheme T.schemeSite S T.scheme_mem).map (φ i)) ∈
      Scheme.fppfPrecoverage ((BigFppfOver.toScheme T.schemeSite S T.scheme_mem).obj W.obj.left)) :
    letI : ∀ i, Algebra ((ringPresheaf (T := T) (V := V)).obj (op W))
        ((ringPresheaf (T := T) (V := V)).obj (op ⟨CostructuredArrow.mk
          ((schemeSpaceFunctor T.schemeSite S T.scheme_mem).map (φ i) ≫ W.obj.hom), hZ i⟩)) :=
      fun i => ((ringPresheaf (T := T) (V := V)).map (homOfScheme W (hZ i) (φ i)).op).hom.toAlgebra
    Module.FaithfullyFlat ((ringPresheaf (T := T) (V := V)).obj (op W))
      (∀ i, (ringPresheaf (T := T) (V := V)).obj (op ⟨CostructuredArrow.mk
          ((schemeSpaceFunctor T.schemeSite S T.scheme_mem).map (φ i) ≫ W.obj.hom), hZ i⟩)) :=
  faithfullyFlat_pi_of_fppf W
    (fun i => ⟨CostructuredArrow.mk
      ((schemeSpaceFunctor T.schemeSite S T.scheme_mem).map (φ i) ≫ W.obj.hom), hZ i⟩)
    (fun i => homOfScheme W (hZ i) (φ i)) hfppf

/-- **The ring of a fibre product is the pushout of the rings.** A commutative square of affine
schemes over `V` whose square of underlying schemes is a fibre product square has a pushout
square of rings of sections of the structure sheaf. -/
theorem isPushout_ringPresheaf {A₀ A₁ A₂ A₃ : AffineSchemesOver T V} {f : A₁ ⟶ A₀}
    {g : A₂ ⟶ A₀} {p₁ : A₃ ⟶ A₁} {p₂ : A₃ ⟶ A₂}
    (h : IsPullback ((BigFppfOver.toScheme T.schemeSite S T.scheme_mem).map p₁.hom.left)
      ((BigFppfOver.toScheme T.schemeSite S T.scheme_mem).map p₂.hom.left)
      ((BigFppfOver.toScheme T.schemeSite S T.scheme_mem).map f.hom.left)
      ((BigFppfOver.toScheme T.schemeSite S T.scheme_mem).map g.hom.left)) :
    IsPushout (CommRingCat.ofHom ((ringPresheaf (T := T) (V := V)).map f.op).hom)
      (CommRingCat.ofHom ((ringPresheaf (T := T) (V := V)).map g.op).hom)
      (CommRingCat.ofHom ((ringPresheaf (T := T) (V := V)).map p₁.op).hom)
      (CommRingCat.ofHom ((ringPresheaf (T := T) (V := V)).map p₂.op).hom) := by
  have h₁ := CommRingCat.isPushout_ulift.{u, u + 1} (isPushout_appTop_of_isPullback h)
  exact h₁.of_iso' (ringIso A₀) (ringIso A₁) (ringIso A₂) (ringIso A₃)
    (ringIso_hom_naturality f).symm (ringIso_hom_naturality g).symm
    (ringIso_hom_naturality p₁).symm (ringIso_hom_naturality p₂).symm

attribute [local instance] BigFppfSite.hasPullbacks_schemes

/-- The member `Z ⟶ W` of a family of affine schemes over an affine scheme `W` over `V`, as an
affine scheme over `V`. -/
abbrev memberObj (W : AffineSchemesOver T V) {Z : T.Schemes}
    (hZ : IsAffine ((BigFppfOver.toScheme T.schemeSite S T.scheme_mem).obj Z))
    (φ : Z ⟶ W.obj.left) : AffineSchemesOver T V :=
  ⟨CostructuredArrow.mk ((schemeSpaceFunctor T.schemeSite S T.scheme_mem).map φ ≫ W.obj.hom), hZ⟩

/-- The fibre product of two schemes over an affine scheme is affine. -/
lemma isAffine_toScheme_pullback {W Z₁ Z₂ : T.Schemes}
    (hW : IsAffine ((BigFppfOver.toScheme T.schemeSite S T.scheme_mem).obj W))
    (hZ₁ : IsAffine ((BigFppfOver.toScheme T.schemeSite S T.scheme_mem).obj Z₁))
    (hZ₂ : IsAffine ((BigFppfOver.toScheme T.schemeSite S T.scheme_mem).obj Z₂))
    (φ₁ : Z₁ ⟶ W) (φ₂ : Z₂ ⟶ W) :
    IsAffine ((BigFppfOver.toScheme T.schemeSite S T.scheme_mem).obj (pullback φ₁ φ₂)) :=
  .of_isPullback ((IsPullback.of_hasPullback φ₁ φ₂).map
    (BigFppfOver.toScheme T.schemeSite S T.scheme_mem))

/-- The fibre product of two members of a family of affine schemes over an affine scheme `W` over
`V`, as an affine scheme over `V`. -/
noncomputable abbrev pairObj (W : AffineSchemesOver T V) {Z₁ Z₂ : T.Schemes}
    (hZ₁ : IsAffine ((BigFppfOver.toScheme T.schemeSite S T.scheme_mem).obj Z₁))
    (hZ₂ : IsAffine ((BigFppfOver.toScheme T.schemeSite S T.scheme_mem).obj Z₂))
    (φ₁ : Z₁ ⟶ W.obj.left) (φ₂ : Z₂ ⟶ W.obj.left) : AffineSchemesOver T V :=
  memberObj (memberObj W hZ₁ φ₁)
    (isAffine_toScheme_pullback W.property hZ₁ hZ₂ φ₁ φ₂) (pullback.fst φ₁ φ₂)

/-- The first projection of `pairObj`. -/
noncomputable abbrev pairFst (W : AffineSchemesOver T V) {Z₁ Z₂ : T.Schemes}
    (hZ₁ : IsAffine ((BigFppfOver.toScheme T.schemeSite S T.scheme_mem).obj Z₁))
    (hZ₂ : IsAffine ((BigFppfOver.toScheme T.schemeSite S T.scheme_mem).obj Z₂))
    (φ₁ : Z₁ ⟶ W.obj.left) (φ₂ : Z₂ ⟶ W.obj.left) :
    pairObj W hZ₁ hZ₂ φ₁ φ₂ ⟶ memberObj W hZ₁ φ₁ :=
  homOfScheme _ _ _

/-- The second projection of `pairObj`. -/
noncomputable abbrev pairSnd (W : AffineSchemesOver T V) {Z₁ Z₂ : T.Schemes}
    (hZ₁ : IsAffine ((BigFppfOver.toScheme T.schemeSite S T.scheme_mem).obj Z₁))
    (hZ₂ : IsAffine ((BigFppfOver.toScheme T.schemeSite S T.scheme_mem).obj Z₂))
    (φ₁ : Z₁ ⟶ W.obj.left) (φ₂ : Z₂ ⟶ W.obj.left) :
    pairObj W hZ₁ hZ₂ φ₁ φ₂ ⟶ memberObj W hZ₂ φ₂ :=
  ObjectProperty.homMk (CostructuredArrow.homMk (pullback.snd φ₁ φ₂) (by
    change (schemeSpaceFunctor T.schemeSite S T.scheme_mem).map (pullback.snd φ₁ φ₂) ≫
        (schemeSpaceFunctor T.schemeSite S T.scheme_mem).map φ₂ ≫ W.obj.hom =
      (schemeSpaceFunctor T.schemeSite S T.scheme_mem).map (pullback.fst φ₁ φ₂) ≫
        (schemeSpaceFunctor T.schemeSite S T.scheme_mem).map φ₁ ≫ W.obj.hom
    rw [← Category.assoc, ← Functor.map_comp, ← pullback.condition, Functor.map_comp,
      Category.assoc]))

/-- The two projections of `pairObj`, followed by the maps to `W`, agree. -/
lemma pairFst_comp (W : AffineSchemesOver T V) {Z₁ Z₂ : T.Schemes}
    (hZ₁ : IsAffine ((BigFppfOver.toScheme T.schemeSite S T.scheme_mem).obj Z₁))
    (hZ₂ : IsAffine ((BigFppfOver.toScheme T.schemeSite S T.scheme_mem).obj Z₂))
    (φ₁ : Z₁ ⟶ W.obj.left) (φ₂ : Z₂ ⟶ W.obj.left) :
    pairFst W hZ₁ hZ₂ φ₁ φ₂ ≫ homOfScheme W hZ₁ φ₁ =
      pairSnd W hZ₁ hZ₂ φ₁ φ₂ ≫ homOfScheme W hZ₂ φ₂ :=
  ObjectProperty.hom_ext _ (CostructuredArrow.hom_ext _ _ pullback.condition)

/-- The rings of the members of a family of affine schemes over `W` and of their pairwise fibre
products form pushout squares. -/
theorem isPushout_pair (W : AffineSchemesOver T V) {Z₁ Z₂ : T.Schemes}
    (hZ₁ : IsAffine ((BigFppfOver.toScheme T.schemeSite S T.scheme_mem).obj Z₁))
    (hZ₂ : IsAffine ((BigFppfOver.toScheme T.schemeSite S T.scheme_mem).obj Z₂))
    (φ₁ : Z₁ ⟶ W.obj.left) (φ₂ : Z₂ ⟶ W.obj.left) :
    IsPushout (CommRingCat.ofHom ((ringPresheaf (T := T) (V := V)).map
        (homOfScheme W hZ₁ φ₁).op).hom)
      (CommRingCat.ofHom ((ringPresheaf (T := T) (V := V)).map (homOfScheme W hZ₂ φ₂).op).hom)
      (CommRingCat.ofHom ((ringPresheaf (T := T) (V := V)).map
        (pairFst W hZ₁ hZ₂ φ₁ φ₂).op).hom)
      (CommRingCat.ofHom ((ringPresheaf (T := T) (V := V)).map
        (pairSnd W hZ₁ hZ₂ φ₁ φ₂).op).hom) :=
  isPushout_ringPresheaf ((IsPullback.of_hasPullback φ₁ φ₂).map
    (BigFppfOver.toScheme T.schemeSite S T.scheme_mem))

/-- **The base change presheaf is a sheaf for a finite fppf family of affine schemes over `V`.**
-/
theorem isSheafFor_baseChangePresheaf {W₀ : AffineSchemesOver T V} (hW₀ : IsTerminal W₀)
    (M : ModuleCat.{u + 1} ((ringPresheaf (T := T) (V := V)).obj (op W₀)))
    (W : AffineSchemesOver T V) {n : ℕ} (Z : Fin n → T.Schemes)
    (hZ : ∀ i, IsAffine ((BigFppfOver.toScheme T.schemeSite S T.scheme_mem).obj (Z i)))
    (φ : ∀ i, Z i ⟶ W.obj.left)
    (hfppf : Presieve.ofArrows
        (fun i => (BigFppfOver.toScheme T.schemeSite S T.scheme_mem).obj (Z i))
        (fun i => (BigFppfOver.toScheme T.schemeSite S T.scheme_mem).map (φ i)) ∈
      Scheme.fppfPrecoverage ((BigFppfOver.toScheme T.schemeSite S T.scheme_mem).obj W.obj.left)) :
    Presieve.IsSheafFor
      (((Stacks.TerminalBaseChange.baseChangePresheaf.{u + 1} (ringPresheaf (T := T) (V := V))
          hW₀).obj M).presheaf ⋙ CategoryTheory.forget AddCommGrpCat.{u + 1})
      (Presieve.ofArrows _ (fun i => homOfScheme W (hZ i) (φ i))) :=
  Stacks.TerminalBaseChange.isSheafFor_baseChangePresheaf_ofArrows _ hW₀ M
    (fun i => homOfScheme W (hZ i) (φ i)) (fun i j => pairFst W (hZ i) (hZ j) (φ i) (φ j))
    (fun i j => pairSnd W (hZ i) (hZ j) (φ i) (φ j))
    (fun i j => pairFst_comp W (hZ i) (hZ j) (φ i) (φ j))
    (faithfullyFlat_pi W Z hZ φ hfppf)
    (fun i j => isPushout_pair W (hZ i) (hZ j) (φ i) (φ j))

/-- **The base change presheaf is a sheaf on the affine schemes over `V`**: for a terminal affine
scheme `W₀` over `V` and a module `M` over its ring, `A ↦ 𝒪(A) ⊗_{𝒪(W₀)} M` is a sheaf. -/
theorem isSheaf_baseChangePresheaf {W₀ : AffineSchemesOver T V} (hW₀ : IsTerminal W₀)
    (M : ModuleCat.{u + 1} ((ringPresheaf (T := T) (V := V)).obj (op W₀))) :
    Presheaf.IsSheaf (topology (T := T) (V := V))
      ((Stacks.TerminalBaseChange.baseChangePresheaf.{u + 1} (ringPresheaf (T := T) (V := V))
          hW₀).obj M).presheaf := by
  rw [Presheaf.isSheaf_iff_isSheaf_forget _ _ (CategoryTheory.forget AddCommGrpCat.{u + 1}),
    isSheaf_iff_isSheaf_of_type]
  have hsep : ∀ ⦃W : AffineSchemesOver T V⦄ (R : Sieve W), R ∈ topology (T := T) (V := V) W →
      Presieve.IsSeparatedFor
        (((Stacks.TerminalBaseChange.baseChangePresheaf.{u + 1}
          (ringPresheaf (T := T) (V := V)) hW₀).obj M).presheaf ⋙
            CategoryTheory.forget AddCommGrpCat.{u + 1}) (R : Presieve W) := by
    intro W R hR
    obtain ⟨n, Z, hZ, φ, hRφ, -, hfppf⟩ := exists_finite_fppf_ofArrows_le W R hR
    refine (isSheafFor_baseChangePresheaf hW₀ M W Z hZ φ hfppf).isSeparatedFor.of_le ?_
    rintro _ _ ⟨i⟩
    exact hRφ i
  intro W R hR
  obtain ⟨n, Z, hZ, φ, hRφ, hcov, hfppf⟩ := exists_finite_fppf_ofArrows_le W R hR
  exact Presheaf.isSheafFor_of_exists_isSheafFor_le _ _ hsep R _ hRφ hcov
    (isSheafFor_baseChangePresheaf hW₀ M W Z hZ φ hfppf)

/-- **The base change presheaf is a sheaf for every module**, at the terminal affine scheme over
`V` given by an identification of `V` with an affine scheme. -/
theorem baseChangeIsSheaf (V₀ : T.Schemes)
    (hV₀ : IsAffine ((BigFppfOver.toScheme T.schemeSite S T.scheme_mem).obj V₀))
    (e : (schemeSpaceFunctor T.schemeSite S T.scheme_mem).obj V₀ ≅ V.left) :
    Stacks.DenseSubsiteBaseChange.BaseChangeIsSheaf (topology (T := T) (V := V))
      ((BigFppfSpaceOver.topology T X).over V) (toSlice T V) sliceRingSheaf
      (isTerminalOfIso V₀ hV₀ e) :=
  fun M => isSheaf_baseChangePresheaf _ M

set_option synthInstance.maxHeartbeats 400000 in
/-- **The sheaf of modules `M^a` on the slice `(Spaces/X)_fppf/V`** attached to a module `M` over
the ring of an affine scheme `V₀` identified with `V`: the unique sheaf of modules whose sections
over an affine scheme `A` over `V` are `𝒪(A) ⊗_{𝒪(V₀)} M`. -/
noncomputable def associatedSheaf (V₀ : T.Schemes)
    (hV₀ : IsAffine ((BigFppfOver.toScheme T.schemeSite S T.scheme_mem).obj V₀))
    (e : (schemeSpaceFunctor T.schemeSite S T.scheme_mem).obj V₀ ≅ V.left) :
    ModuleCat.{u + 1} ((ringPresheaf (T := T) (V := V)).obj (op (ofIso V₀ hV₀ e))) ⥤
      SheafOfModules.{u + 1} (sliceRingSheaf (T := T) (V := V)) :=
  Stacks.DenseSubsiteBaseChange.associatedSheaf (baseChangeIsSheaf V₀ hV₀ e)

end AlgebraicGeometry.BigFppfSpaceSite.AffineSchemesOver

end
