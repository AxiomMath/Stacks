module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SheafificationTensor

public import
  StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedPushforwardSheafHomExact
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedToposDerivedPushforward

/-!
# The exact functor `ℳ ↦ f_*SheafHom^dg_{𝒜'}(𝒩, ℳ)` along a morphism of ringed topoi

Let `(f, f♯) : (Sh(𝒞), O_𝒞) ⟶ (Sh(𝒟), O_𝒟)` be a morphism of ringed topoi, let `𝒜` and `𝒜'` be
sheaves of differential graded `O_𝒞`-algebras, let `ℬ` be a sheaf of differential graded
`O_𝒟`-algebras, let `φ : ℬ ⟶ f_*𝒜` be a unital homomorphism and let `𝒩` be a differential graded
`(𝒜, 𝒜')`-bimodule. The functor

`Mod(𝒜', d) ⥤ Mod(ℬ, d)`, `ℳ ↦ f_*SheafHom^dg_{𝒜'}(𝒩, ℳ)`

extends to homogeneous maps: the internal hom postcomposes, and the direct image — the transport
along the additive lax monoidal direct image of sheaves of modules followed by restriction of
scalars along `φ` — is applied degreewise. So it is a functor of differential graded categories,
and it induces an exact functor

`K(Mod(𝒜', d)) ⥤ K(Mod(ℬ, d))`

of triangulated categories, which is [Stacks, Tag 0FTS](https://stacks.math.columbia.edu/tag/0FTS).

## Main definitions

* `SheafOfModules.DifferentialGradedModule.transportConcreteDGFunctor`: the transport along an
  additive lax monoidal functor, extended to homogeneous maps degreewise.
* `SheafOfModules.DifferentialGradedModule.restrictScalarsConcreteDGFunctor`: restriction of
  scalars, extended to homogeneous maps.
* `SheafOfModules.DifferentialGradedModule.toposPushforwardConcreteDGFunctor`: the direct image
  along a morphism of ringed topoi, extended to homogeneous maps.
* `SheafOfModules.DifferentialGradedModule.homotopyToposPushforwardSheafHom`: the functor
  `K(Mod(𝒜', d)) ⥤ K(Mod(ℬ, d))` of the tag, with its `Functor.CommShift ℤ` and
  `Functor.IsTriangulated` instances.

## Main results

* `SheafOfModules.DifferentialGradedModule.smulSheaf_comp_heq_iff_degree`: a degreewise family
  of morphisms raising the degree by `k` commutes with the morphism-level actions exactly when it
  preserves the action on local sections.
* `exists_isTriangulated_homotopyToposPushforwardSheafHomTopos` (in the same namespace): Tag 0FTS,
  and `exists_isTriangulated_homotopyToposPushforwardSheafHom` the same with the compatibility
  of `forget₂ CommRingCat RingCat` with sheaves as instance arguments.

## References

* [Stacks Project, Tag 0FTS](https://stacks.math.columbia.edu/tag/0FTS)
* [Stacks Project, Tag 0FQF](https://stacks.math.columbia.edu/tag/0FQF)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CategoryTheory.Sheaf PresheafOfModules
open CategoryTheory.Pretriangulated
open CochainComplex.HomComplex
open scoped TensorProduct

universe u v₁ u₁ w

namespace SheafOfModules.DifferentialGradedModule

/-! ### The action of a homogeneous map at morphism level -/

section Smul

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  {Osharp : Sheaf J CommRingCat.{w}}
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify J AddCommGrpCat.{w}]

attribute [local instance] Stacks.TensorSheafWorld.monoidalCategory

variable {A : DifferentialGradedAlgebra.{w, w} (toRingCat J Osharp)}
  (M : DifferentialGradedModule.{w, w, w} A)
  (hO : Presheaf.IsSheaf J
    (Stacks.SheafOfModules.TensorSheafification.structureRingPresheaf Osharp.obj))

omit [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
    [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify J AddCommGrpCat.{w}] in
/-- Two components of a cochain of sheaves of modules with equal targets agree on sections,
heterogeneously. -/
theorem cochain_v_app_heq_of_eq {R : Sheaf J RingCat.{w}}
    {K L : CochainComplex (SheafOfModules.{w} R) ℤ} {k : ℤ} (c : Cochain K L k) {p q q' : ℤ}
    (h : q = q') (hp : p + k = q) (hp' : p + k = q') (U : Cᵒᵖ) (x : (K.X p).val.obj U) :
    HEq ((c.v p q hp).val.app U x) ((c.v p q' hp').val.app U x) := by
  subst h
  rfl

include hO in
/-- **A degreewise family of morphisms of sheaves of modules raising the degree by `k` commutes
with the morphism-level actions if and only if it preserves the action on local sections.** The
transport `eqToHom` identifies the two readings `(n + i) + k` and `(n + k) + i` of the target
degree. -/
theorem smulSheaf_comp_heq_iff_degree (N : DifferentialGradedModule.{w, w, w} A) (k : ℤ)
    (φ : ∀ n : ℤ, M.complex.X n ⟶ N.complex.X (n + k)) (n i : ℤ) :
    smulSheaf M n i ≫ φ (n + i) ≫
          eqToHom (congrArg N.complex.X (show n + i + k = n + k + i by omega)) =
        (φ n ⊗ₘ 𝟙 (A.complex.X i)) ≫ smulSheaf N (n + k) i ↔
      ∀ (U : Cᵒᵖ) (x : (M.complex.X n).val.obj U) (y : (A.complex.X i).val.obj U),
        HEq ((φ (n + i)).val.app U ((M.mul n i).app U x y))
          ((N.mul (n + k) i).app U ((φ n).val.app U x) y) := by
  have hd : n + i + k = n + k + i := by omega
  have key : ∀ (U : Cᵒᵖ) (x : (M.complex.X n).val.obj U) (y : (A.complex.X i).val.obj U),
      ((smulSheaf M n i ≫ φ (n + i) ≫ eqToHom (congrArg N.complex.X hd)).val.app U
          ((tensorSheafUnit (M.complex.X n) (A.complex.X i)).app U (x ⊗ₜ y)) =
        ((φ n ⊗ₘ 𝟙 (A.complex.X i)) ≫ smulSheaf N (n + k) i).val.app U
          ((tensorSheafUnit (M.complex.X n) (A.complex.X i)).app U (x ⊗ₜ y))) ↔
      HEq ((φ (n + i)).val.app U ((M.mul n i).app U x y))
        ((N.mul (n + k) i).app U ((φ n).val.app U x) y) := by
    intro U x y
    have hL : (smulSheaf M n i ≫ φ (n + i) ≫ eqToHom (congrArg N.complex.X hd)).val.app U
            ((tensorSheafUnit (M.complex.X n) (A.complex.X i)).app U (x ⊗ₜ y)) =
        (eqToHom (congrArg N.complex.X hd)).val.app U
          ((φ (n + i)).val.app U ((M.mul n i).app U x y)) :=
      congrArg (fun t ↦ (eqToHom (congrArg N.complex.X hd)).val.app U ((φ (n + i)).val.app U t))
        (smulSheaf_unit M n i U x y)
    have hR : ((φ n ⊗ₘ 𝟙 (A.complex.X i)) ≫ smulSheaf N (n + k) i).val.app U
            ((tensorSheafUnit (M.complex.X n) (A.complex.X i)).app U (x ⊗ₜ y)) =
        (N.mul (n + k) i).app U ((φ n).val.app U x) y :=
      (congrArg ((smulSheaf N (n + k) i).val.app U)
          (Stacks.TensorSheafWorld.tensorHom_val_app_tensorSheafUnit Osharp hO U
            (φ n) (𝟙 (A.complex.X i)) x y)).trans
        (smulSheaf_unit N (n + k) i U ((φ n).val.app U x) y)
    rw [hL, hR]
    exact ⟨fun h ↦ (Stacks.TensorSheafWorld.heq_eqToHom_val_app N.complex.X hd U _).symm.trans
        (heq_of_eq h),
      fun h ↦ eq_of_heq ((Stacks.TensorSheafWorld.heq_eqToHom_val_app N.complex.X hd U _).trans h)⟩
  refine ⟨fun h U x y ↦ ?_, fun h ↦ ?_⟩
  · exact (key U x y).mp (congrArg (fun ψ : ((Stacks.SheafOfModules.Tensor.sheafTensor Osharp).obj
        (M.complex.X n)).obj (A.complex.X i) ⟶ N.complex.X (n + k + i) ↦
      ψ.val.app U ((tensorSheafUnit (M.complex.X n) (A.complex.X i)).app U (x ⊗ₜ y))) h)
  · exact PresheafOfModules.tensorSheaf_hom_ext (Osharp := Osharp) (F := M.complex.X n)
      (G := A.complex.X i) (Q := N.complex.X (n + k + i)) fun U x y ↦ (key U x y).mpr (h U x y)

end Smul

/-! ### Transport and restriction of scalars, extended to homogeneous maps -/

section Concrete

open Stacks.Sheaves.RingedToposModules

attribute [local instance] Stacks.TensorSheafWorld.monoidalCategory
  AlgebraicGeometry.RingedTopos.hasSheafify_addCommGrpCat
  AlgebraicGeometry.RingedTopos.wEqualsLocallyBijective_addCommGrpCat

variable {X Y : AlgebraicGeometry.RingedTopos.{u, u, u}}
  [X.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]

/-- The sheaf condition on the structure ring presheaf of a ringed topos, which the transport
along a lax monoidal functor takes as an argument. -/
theorem isSheaf_structureRingPresheaf_topos (X : AlgebraicGeometry.RingedTopos.{u, u, u})
    [X.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})] :
    Presheaf.IsSheaf X.J
      (Stacks.SheafOfModules.TensorSheafification.structureRingPresheaf X.O.obj) :=
  Stacks.SheafOfModules.TensorEncodings.isSheaf_structureRingPresheaf X.O

variable (L : SheafOfModules.{u} (toRingCat X.J X.O) ⥤ SheafOfModules.{u} (toRingCat Y.J Y.O))
  [L.LaxMonoidal] [L.Additive] (A : DifferentialGradedAlgebra.{u, u} (toRingCat X.J X.O))

/-- The transport of `A` along `L`, a sheaf of differential graded algebras on `Y`. -/
noncomputable abbrev transportAlgebra : DifferentialGradedAlgebra.{u, u} (toRingCat Y.J Y.O) :=
  DifferentialGradedAlgebra.transport L (isSheaf_structureRingPresheaf_topos X)
    (isSheaf_structureRingPresheaf_topos Y) A

/-- An action-linear cochain of degree `k`, read as a degreewise family of morphisms raising the
degree by `k`, preserves the action on local sections in the form of
`smulSheaf_comp_heq_iff_degree`. -/
theorem isActionLinear_degreewise {M N : DifferentialGradedModule.{u, u, u} A} {k : ℤ}
    (c : Cochain M.complex N.complex k)
    (hc : IsActionLinear (X := X.toRingedSite) A c) (n i : ℤ) (U : X.Cᵒᵖ)
    (x : (M.complex.X n).val.obj U) (y : (A.complex.X i).val.obj U) :
    HEq ((c.v (n + i) (n + i + k) rfl).val.app U ((M.mul n i).app U x y))
      ((N.mul (n + k) i).app U ((c.v n (n + k) rfl).val.app U x) y) :=
  (cochain_v_app_heq_of_eq c (show n + i + k = n + k + i by omega) rfl (by omega) U _).trans
    (hc n (n + k) i rfl U x y)

/-- The transport of a cochain: the functor applied degreewise. -/
noncomputable abbrev transportCochain {M N : DifferentialGradedModule.{u, u, u} A} {k : ℤ}
    (c : Cochain M.complex N.complex k) :
    Cochain (transport L M (isSheaf_structureRingPresheaf_topos X)
        (isSheaf_structureRingPresheaf_topos Y)).complex
      (transport L N (isSheaf_structureRingPresheaf_topos X)
        (isSheaf_structureRingPresheaf_topos Y)).complex k :=
  c.map L

/-- **The transport of an action-linear cochain is action-linear.** The cochain is action-linear
exactly when its morphism-level form commutes with the actions, a lax monoidal functor transports
that equation by the naturality of its tensorator, and the transported equation is the
action-linearity of the transported cochain. -/
theorem isActionLinear_map_transport {M N : DifferentialGradedModule.{u, u, u} A} {k : ℤ}
    (c : Cochain M.complex N.complex k) (hc : IsActionLinear (X := X.toRingedSite) A c) :
    IsActionLinear (X := Y.toRingedSite) (transportAlgebra L A)
      (M := transport L M (isSheaf_structureRingPresheaf_topos X)
        (isSheaf_structureRingPresheaf_topos Y))
      (N := transport L N (isSheaf_structureRingPresheaf_topos X)
        (isSheaf_structureRingPresheaf_topos Y)) (transportCochain L A c) := by
  intro p q m hpq U x a
  subst hpq
  have hO := isSheaf_structureRingPresheaf_topos X
  have hP := isSheaf_structureRingPresheaf_topos Y
  have hd : p + m + k = p + k + m := by omega
  have hsrc : smulSheaf M p m ≫ c.v (p + m) (p + m + k) rfl ≫
        eqToHom (congrArg N.complex.X hd) =
      (c.v p (p + k) rfl ⊗ₘ 𝟙 (A.complex.X m)) ≫ smulSheaf N (p + k) m :=
    (smulSheaf_comp_heq_iff_degree M hO N k (fun q => c.v q (q + k) rfl) p m).mpr
      (isActionLinear_degreewise A c hc p m)
  have hnat := Stacks.MonoidalGraded.mapMul_naturality L (smulSheaf M p m)
    (smulSheaf N (p + k) m) (c.v p (p + k) rfl) (𝟙 (A.complex.X m))
    (c.v (p + m) (p + m + k) rfl ≫
      eqToHom (congrArg N.complex.X hd)) hsrc
  rw [L.map_comp, L.map_id, eqToHom_map] at hnat
  have h := (smulSheaf_comp_heq_iff_degree (transport L M hO hP) hP (transport L N hO hP) k
    (fun q => L.map (c.v q (q + k) rfl)) p m).mp
      (by rwa [smulSheaf_transport, smulSheaf_transport]) U x a
  exact (cochain_v_app_heq_of_eq (c.map L) hd.symm _ rfl U
    _).trans h

/-- The transport of cochains is additive. -/
theorem transportCochain_add {M N : DifferentialGradedModule.{u, u, u} A} {k : ℤ}
    (c c' : Cochain M.complex N.complex k) :
    transportCochain L A (c + c') = transportCochain L A c + transportCochain L A c' :=
  Cochain.map_add _ _ _

/-- The transport of cochains commutes with the differentials of the hom complexes. -/
theorem transportCochain_delta {M N : DifferentialGradedModule.{u, u, u} A} {k : ℤ}
    (c : Cochain M.complex N.complex k) :
    transportCochain L A (δ k (k + 1) c) = δ k (k + 1) (transportCochain L A c) :=
  (δ_map _ _ _ _).symm

/-- The transport of cochains preserves composition. -/
theorem transportCochain_comp {M N P : DifferentialGradedModule.{u, u, u} A} {k l m : ℤ}
    (c : Cochain M.complex N.complex k) (c' : Cochain N.complex P.complex l) (h : k + l = m) :
    transportCochain L A (c.comp c' h) =
      (transportCochain L A c).comp (transportCochain L A c') h :=
  Cochain.map_comp (z₁ := c) (z₂ := c') (h := h) (Φ := L) ..

/-- The transport of the cochain of a morphism is the cochain of the transported morphism. -/
theorem transportCochain_ofHom {M N : DifferentialGradedModule.{u, u, u} A} (g : M ⟶ N) :
    transportCochain L A (Cochain.ofHom g.toHomologicalComplex) =
      Cochain.ofHom ((transportFunctor L (isSheaf_structureRingPresheaf_topos X)
        (isSheaf_structureRingPresheaf_topos Y)).map g).toHomologicalComplex :=
  Cochain.map_ofHom _ _ g.toHomologicalComplex _

/-- **The transport along an additive lax monoidal functor, extended to homogeneous maps**: a
cochain is transported degreewise. -/
noncomputable def transportConcreteDGFunctor :
    ConcreteDGFunctor.{u, u, u, u, u} (X := X.toRingedSite) (Y := Y.toRingedSite) A
      (transportAlgebra L A) where
  functor := transportFunctor L (isSheaf_structureRingPresheaf_topos X)
    (isSheaf_structureRingPresheaf_topos Y)
  mapCochain c _ := transportCochain L A c
  isActionLinear_mapCochain c hc := isActionLinear_map_transport L A c hc
  mapCochain_add c c' _ _ _ := transportCochain_add L A c c'
  mapCochain_delta c _ _ := transportCochain_delta L A c
  mapCochain_comp c c' h _ _ _ := transportCochain_comp L A c c' h
  mapCochain_ofHom g := transportCochain_ofHom L A g

variable {A} in
/-- **Restriction of scalars along a unital homomorphism, extended to homogeneous maps**: a
cochain is left as it is. -/
noncomputable def restrictScalarsConcreteDGFunctor
    {B : DifferentialGradedAlgebra.{u, u} (toRingCat X.J X.O)} (φ : A ⟶ B) (hφ : φ.IsUnital) :
    ConcreteDGFunctor.{u, u, u, u, u} (X := X.toRingedSite) (Y := X.toRingedSite) B A where
  functor := restrictScalars φ hφ
  mapCochain c _ := c
  isActionLinear_mapCochain _ hc p q m hpq U x a :=
    hc p q m hpq U x ((φ.toHomologicalComplex.f m).val.app U a)
  mapCochain_add _ _ _ _ _ := rfl
  mapCochain_delta _ _ _ := rfl
  mapCochain_comp _ _ _ _ _ _ := rfl
  mapCochain_ofHom _ := rfl

end Concrete

/-! ### The homotopy category over the site of a ringed topos -/

section Instances

variable {X : AlgebraicGeometry.RingedTopos.{u, u, u}}
  [X.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  (A : DifferentialGradedAlgebra.{u, u} (toRingCat X.J X.O))

/-- The rings of sections of the structure sheaf of a ringed topos are commutative. -/
instance _root_.AlgebraicGeometry.RingedTopos.instIsMulCommutativeToRingCatObj
    (U : X.Cᵒᵖ) : IsMulCommutative ((toRingCat X.J X.O).obj.obj U) :=
  AlgebraicGeometry.RingedSite.instIsMulCommutativeRingSheafObj X.toRingedSite U

/-- The translation functors of the homotopy category, over the site of a ringed topos. -/
@[instance_reducible]
noncomputable instance HomotopyCategory.instHasShiftTopos :
    HasShift (HomotopyCategory.{u, u, u} A) ℤ :=
  HomotopyCategory.instHasShift (X := X.toRingedSite) A

/-- The translation functors are additive, over the site of a ringed topos. -/
instance HomotopyCategory.shiftFunctor_additive_topos (n : ℤ) :
    (shiftFunctor (HomotopyCategory.{u, u, u} A) n).Additive :=
  HomotopyCategory.shiftFunctor_additive (X := X.toRingedSite) A n

/-- The homotopy category is pretriangulated, over the site of a ringed topos. -/
@[instance_reducible]
noncomputable instance HomotopyCategory.instPretriangulatedTopos :
    Pretriangulated (HomotopyCategory.{u, u, u} A) :=
  HomotopyCategory.instPretriangulated (X := X.toRingedSite) A

/-- The homotopy category is triangulated, over the site of a ringed topos. -/
instance HomotopyCategory.instIsTriangulatedTopos :
    IsTriangulated (HomotopyCategory.{u, u, u} A) :=
  HomotopyCategory.instIsTriangulated (X := X.toRingedSite) A

end Instances

/-! ### Tag 0FTS -/

section Main

open Stacks.Sheaves.RingedToposModules

attribute [local instance] Stacks.TensorSheafWorld.monoidalCategory
  AlgebraicGeometry.RingedTopos.hasSheafify_addCommGrpCat
  AlgebraicGeometry.RingedTopos.wEqualsLocallyBijective_addCommGrpCat

variable {X Y : AlgebraicGeometry.RingedTopos.{u, u, u}}
  [X.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})] (f : RingedToposHom X Y)
  {A A' : DifferentialGradedAlgebra.{u, u} (toRingCat X.J X.O)}
  {B : DifferentialGradedAlgebra.{u, u} (toRingCat Y.J Y.O)}
  (φ : B ⟶ toposPushforwardAlgebra (toposDirectImageModules f) A) (hφ : φ.IsUnital)

/-- **The direct image along a morphism of ringed topoi, extended to homogeneous maps.** -/
noncomputable def toposPushforwardConcreteDGFunctor :
    ConcreteDGFunctor.{u, u, u, u, u} (X := X.toRingedSite) (Y := Y.toRingedSite) A B :=
  (transportConcreteDGFunctor (toposDirectImageModules f) A).comp
    (restrictScalarsConcreteDGFunctor φ hφ)

/-- **The functor `ℳ ↦ f_*SheafHom^dg_{𝒜'}(𝒩, ℳ)` along a morphism of ringed topoi, extended to
homogeneous maps.** -/
noncomputable def toposPushforwardSheafHomConcreteDGFunctor
    (N : DifferentialGradedBimodule.{u, u, u} A A') :
    ConcreteDGFunctor.{u, u, u, u, u} (X := X.toRingedSite) (Y := Y.toRingedSite) A' B :=
  (sheafHomConcreteDGFunctor.{u, u, u, u} (X := X.toRingedSite) N).comp
    (toposPushforwardConcreteDGFunctor f φ hφ)

/-- **The functor `K(Mod(𝒜', d)) ⥤ K(Mod(ℬ, d))`, `ℳ ↦ f_*SheafHom^dg_{𝒜'}(𝒩, ℳ)`**, along a
morphism of ringed topoi, on homotopy categories. -/
noncomputable def homotopyToposPushforwardSheafHom
    (N : DifferentialGradedBimodule.{u, u, u} A A') :
    HomotopyCategory.{u, u, u} A' ⥤ HomotopyCategory.{u, u, u} B :=
  (toposPushforwardSheafHomConcreteDGFunctor f φ hφ N).homotopyFunctor

/-- The functor of Tag 0FTS factors `ℳ ↦ f_*SheafHom^dg_{𝒜'}(𝒩, ℳ)` through the two quotient
functors. -/
theorem quotient_comp_homotopyToposPushforwardSheafHom
    (N : DifferentialGradedBimodule.{u, u, u} A A') :
    HomotopyCategory.quotient A' ⋙ homotopyToposPushforwardSheafHom f φ hφ N =
      (sheafHomFunctor N ⋙ toposPushforward (toposDirectImageModules f) φ hφ) ⋙
        HomotopyCategory.quotient B :=
  (toposPushforwardSheafHomConcreteDGFunctor f φ hφ N).quotient_comp_homotopyFunctor

/-- The functor of Tag 0FTS commutes with the translations. -/
@[instance_reducible]
noncomputable instance homotopyToposPushforwardSheafHom_commShift
    (N : DifferentialGradedBimodule.{u, u, u} A A') :
    (homotopyToposPushforwardSheafHom f φ hφ N).CommShift ℤ :=
  (toposPushforwardSheafHomConcreteDGFunctor f φ hφ N).commShift

/-- The functor of Tag 0FTS is a triangulated functor. -/
instance homotopyToposPushforwardSheafHom_isTriangulated
    (N : DifferentialGradedBimodule.{u, u, u} A A') :
    (homotopyToposPushforwardSheafHom f φ hφ N).IsTriangulated :=
  (toposPushforwardSheafHomConcreteDGFunctor f φ hφ N).isTriangulated

/-- **The exact functor of Tag 0FTS, with the compatibility of `forget₂ CommRingCat RingCat` with
sheaves as instance arguments.** The statement of
[Stacks, Tag 0FTS](https://stacks.math.columbia.edu/tag/0FTS) itself, in which that
compatibility is discharged, is `exists_isTriangulated_homotopyToposPushforwardSheafHomTopos`. -/
theorem exists_isTriangulated_homotopyToposPushforwardSheafHom
    (N : DifferentialGradedBimodule.{u, u, u} A A') :
    ∃ (Φ : HomotopyCategory.{u, u, u} A' ⥤ HomotopyCategory.{u, u, u} B)
      (_ : Φ.CommShift ℤ), Φ.IsTriangulated ∧
      HomotopyCategory.quotient A' ⋙ Φ =
        (sheafHomFunctor N ⋙ toposPushforward (toposDirectImageModules f) φ hφ) ⋙
          HomotopyCategory.quotient B ∧
      ∀ Ψ : HomotopyCategory.{u, u, u} A' ⥤ HomotopyCategory.{u, u, u} B,
        HomotopyCategory.quotient A' ⋙ Ψ =
          (sheafHomFunctor N ⋙ toposPushforward (toposDirectImageModules f) φ hφ) ⋙
            HomotopyCategory.quotient B → Ψ = Φ :=
  ⟨homotopyToposPushforwardSheafHom f φ hφ N, inferInstance, inferInstance,
    quotient_comp_homotopyToposPushforwardSheafHom f φ hφ N,
    fun Ψ hΨ => HomotopyCategory.eq_descend _
      (toposPushforwardSheafHomConcreteDGFunctor f φ hφ N).preservesHomotopic Ψ hΨ⟩

end Main

/-! ### Tag 0FTS -/

section Tag

open Stacks.Sheaves.RingedToposModules

attribute [local instance] Stacks.TensorSheafWorld.monoidalCategory
  AlgebraicGeometry.RingedTopos.hasSheafify_addCommGrpCat
  AlgebraicGeometry.RingedTopos.wEqualsLocallyBijective_addCommGrpCat
  AlgebraicGeometry.RingedTopos.hasSheafCompose_forget₂_ringCat

/-- **Stacks 0FTS.** Let `(f, f♯) : (Sh(𝒞), O_𝒞) ⟶ (Sh(𝒟), O_𝒟)` be a morphism of ringed topoi,
let `𝒜` and `𝒜'` be sheaves of differential graded `O_𝒞`-algebras, let `ℬ` be a sheaf of
differential graded `O_𝒟`-algebras, let `φ : ℬ ⟶ f_*𝒜` be a homomorphism and let `𝒩` be a
differential graded `(𝒜, 𝒜')`-bimodule. Then the functor `ℳ ↦ f_*SheafHom^dg_{𝒜'}(𝒩, ℳ)`
induces an exact functor

`K(Mod(𝒜', d)) ⥤ K(Mod(ℬ, d))`

of triangulated categories: there is a functor `Φ` of homotopy categories through which the
functor of modules factors along the two quotient functors, it is the only one, and it commutes
with the translations and carries distinguished triangles to distinguished triangles.

The homomorphism `φ` is unital, as a homomorphism of differential graded algebras is in the
source; the direct image `f_*` is that of sheaves of modules along `(f, f♯)`, made a functor of
right differential graded modules by transporting the action along its lax monoidal structure
and restricting scalars along `φ`. -/
@[stacks 0FTS]
theorem exists_isTriangulated_homotopyToposPushforwardSheafHomTopos
    {X Y : AlgebraicGeometry.RingedTopos.{u, u, u}} (f : RingedToposHom X Y)
    {A A' : DifferentialGradedAlgebra.{u, u} (toRingCat X.J X.O)}
    {B : DifferentialGradedAlgebra.{u, u} (toRingCat Y.J Y.O)}
    (φ : B ⟶ toposPushforwardAlgebra (Osharp := X.O) (Psharp := Y.O)
      (toposDirectImageModules (X := X) (Y := Y) f) A) (hφ : φ.IsUnital)
    (N : DifferentialGradedBimodule.{u, u, u} A A') :
    ∃ (Φ : HomotopyCategory.{u, u, u} A' ⥤ HomotopyCategory.{u, u, u} B)
      (_ : Φ.CommShift ℤ), Φ.IsTriangulated ∧
      HomotopyCategory.quotient A' ⋙ Φ =
        (sheafHomFunctor N ⋙
          toposPushforward (toposDirectImageModules (X := X) (Y := Y) f) φ hφ) ⋙
          HomotopyCategory.quotient B ∧
      ∀ Ψ : HomotopyCategory.{u, u, u} A' ⥤ HomotopyCategory.{u, u, u} B,
        HomotopyCategory.quotient A' ⋙ Ψ =
          (sheafHomFunctor N ⋙
            toposPushforward (toposDirectImageModules (X := X) (Y := Y) f) φ hφ) ⋙
            HomotopyCategory.quotient B → Ψ = Φ :=
  exists_isTriangulated_homotopyToposPushforwardSheafHom f φ hφ N

end Tag

end SheafOfModules.DifferentialGradedModule
