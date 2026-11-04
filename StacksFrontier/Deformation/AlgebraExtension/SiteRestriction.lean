module

public import StacksFrontier.Deformation.AlgebraExtension.Basic
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import Mathlib.CategoryTheory.Sites.PreservesLocallyBijective

/-!
# Restricting square-zero extensions of sheaves of algebras along a functor of sites

Let `G : 𝒟 ⥤ 𝒞` be a functor of sites which is continuous and cocontinuous, so that restriction
along `G` sends sheaves to sheaves and locally surjective maps to locally surjective maps. An
extension `0 ⟶ ℳ ⟶ 𝒪' ⟶ 𝒪 ⟶ 0` of `𝒜`-algebras on `𝒞` restricts, section by section over the
objects `G(V)`, to an extension of `G^*𝒜`-algebras of `G^*𝒪` by `G^*ℳ` on `𝒟`, and morphisms of
extensions along `φ` restrict to morphisms along `G^*φ`.

The restricted extension is read through identifications `𝒜' ≅ G^*𝒜`, `𝒪' ≅ G^*𝒪` and
`ℳ' ≅ G^*ℳ` (compose the reduction, the structure map and the inclusion of the ideal with them),
so that one construction serves both for restricting to an equivalent site and for coming back.

This is the operation by which the extension categories of the small étale site of an
algebraic space are compared with those of a site equivalent to it, as in the proof of
[Stacks Project, Tag 0D3P].

## Main definitions

* `Deformation.AlgebraExtension.RingComparison`: an identification of base data `𝒜' ⟶ 𝒪'` on `𝒟`
  with the restriction of `𝒜 ⟶ 𝒪`.
* `Deformation.AlgebraExtension.ModuleComparison`: an identification of a module `ℳ'` on `𝒟` with
  the restriction of `ℳ`.
* `Deformation.AlgebraExtension.restrictVia`: the restriction of an extension along `G`, read
  through such identifications.
* `Deformation.AlgebraExtension.MapAlong.restrictVia`: the restriction of a morphism of extensions.
* `Deformation.AlgebraExtension.restrictViaFunctor`: restriction as a functor.

## References

* [Stacks Project, Tag 0D3P](https://stacks.math.columbia.edu/tag/0D3P)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u v₁ w₁ v₂ w₂

namespace Deformation.AlgebraExtension

/-! ### Restriction along a functor of sites -/

section Restrict

variable {C : Type v₁} [Category.{w₁} C] {D : Type v₂} [Category.{w₂} D]
  {J : GrothendieckTopology C} (K : GrothendieckTopology D) (G : D ⥤ C)
  [G.IsContinuous K J] [G.IsCocontinuous K J]
  [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [K.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  {A O : Sheaf J CommRingCat.{u}}

/-- Restriction of sheaves of commutative rings along `G`. -/
abbrev ringRes : Sheaf J CommRingCat.{u} ⥤ Sheaf K CommRingCat.{u} :=
  G.sheafPushforwardContinuous CommRingCat.{u} K J

/-- Restriction along `G` of sheaves of modules over a sheaf of commutative rings `𝒪`, to
sheaves of modules over `G^*𝒪`. -/
noncomputable abbrev moduleRes (O : Sheaf J CommRingCat.{u}) :
    SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj O) ⥤
      SheafOfModules.{u} ((sheafCompose K (forget₂ CommRingCat.{u} RingCat.{u})).obj
        ((ringRes K G).obj O)) :=
  SheafOfModules.pushforward.{u}
    (𝟙 ((G.sheafPushforwardContinuous RingCat.{u} K J).obj
      ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj O)))

variable {K G} {A' O' : Sheaf K CommRingCat.{u}}

/-- **A comparison of base data along `G`**: sheaves of rings `𝒜' ⟶ 𝒪'` on `𝒟` identified with the
restrictions `G^*𝒜 ⟶ G^*𝒪`. -/
structure RingComparison (a : A ⟶ O) (a' : A' ⟶ O') where
  /-- `𝒜' ≅ G^*𝒜`. -/
  α : A' ≅ (ringRes K G).obj A
  /-- `𝒪' ≅ G^*𝒪`. -/
  ω : O' ≅ (ringRes K G).obj O
  /-- The two identifications are compatible with the structure maps. -/
  comm : a' ≫ ω.hom = α.hom ≫ (ringRes K G).map a

/-- **A comparison of modules along a comparison of rings**: an `𝒪'`-module `ℳ'` identified,
section by section and compatibly with restriction and scalars, with the restriction of the
`𝒪`-module `ℳ`. -/
structure ModuleComparison (ω : O' ≅ (ringRes K G).obj O)
    (M : SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj O))
    (M' : SheafOfModules.{u} ((sheafCompose K (forget₂ CommRingCat.{u} RingCat.{u})).obj O')) where
  /-- The identification of sections. -/
  μ : ∀ V : Dᵒᵖ, M'.val.obj V ≃+ M.val.obj (G.op.obj V)
  /-- It commutes with restriction. -/
  μ_naturality : ∀ {V W : Dᵒᵖ} (f : V ⟶ W) (m : M'.val.obj V),
    μ W (M'.val.map f m) = M.val.map (G.op.map f) (μ V m)
  /-- It is semilinear along `ω`. -/
  μ_smul : ∀ (V : Dᵒᵖ) (r : O'.obj.obj V) (m : M'.val.obj V),
    μ V (scalar r • m) = scalar (O := O) (U := G.op.obj V) (ω.hom.hom.app V r) • μ V m

variable {a : A ⟶ O} {a' : A' ⟶ O'}
  {M N : SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj O)}
  {M' N' : SheafOfModules.{u} ((sheafCompose K (forget₂ CommRingCat.{u} RingCat.{u})).obj O')}

omit [G.IsCocontinuous K J] [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [K.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})] in
/-- `ω.hom` is a left inverse of `ω.inv` on sections over `V`. -/
theorem RingComparison.ω_hom_inv (c : RingComparison (G := G) a a') (V : Dᵒᵖ)
    (y : O.obj.obj (G.op.obj V)) : c.ω.hom.hom.app V (c.ω.inv.hom.app V y) = y :=
  congrArg (fun k : (ringRes K G).obj O ⟶ (ringRes K G).obj O => k.hom.app V y) c.ω.inv_hom_id

omit [G.IsCocontinuous K J] [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [K.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})] in
/-- `ω.inv` is a left inverse of `ω.hom` on sections over `V`. -/
theorem RingComparison.ω_inv_hom (c : RingComparison (G := G) a a') (V : Dᵒᵖ)
    (y : O'.obj.obj V) : c.ω.inv.hom.app V (c.ω.hom.hom.app V y) = y :=
  congrArg (fun k : O' ⟶ O' => k.hom.app V y) c.ω.hom_inv_id

/-- The inclusion `ℳ'(V) ⟶ 𝒪'(G V)` of a restricted extension: `m ↦ ι(μ m)`. -/
noncomputable def inclVia {c : RingComparison (G := G) a a'} (cM : ModuleComparison c.ω M M')
    (P : AlgebraExtension a M) (V : Dᵒᵖ) (m : M'.val.obj V) : P.extension.obj.obj (G.op.obj V) :=
  P.incl (cM.μ V m)

omit [G.IsCocontinuous K J] in
/-- `inclVia` is additive. -/
theorem inclVia_add {c : RingComparison (G := G) a a'} (cM : ModuleComparison c.ω M M')
    (P : AlgebraExtension a M) (V : Dᵒᵖ) (m n : M'.val.obj V) :
    inclVia cM P V (m + n) = inclVia cM P V m + inclVia cM P V n :=
  (congrArg P.incl (map_add (cM.μ V) m n)).trans (P.incl_add _ _)

omit [G.IsCocontinuous K J] in
/-- `inclVia` turns the action of the image of `x` under the reduction and `ω⁻¹` into
multiplication by `x`. -/
theorem inclVia_smul {c : RingComparison (G := G) a a'} (cM : ModuleComparison c.ω M M')
    (P : AlgebraExtension a M) (V : Dᵒᵖ) (x : P.extension.obj.obj (G.op.obj V))
    (m : M'.val.obj V) :
    inclVia cM P V (scalar (c.ω.inv.hom.app V (P.reduction.hom.app (G.op.obj V) x)) • m) =
      x * inclVia cM P V m := by
  unfold inclVia
  rw [cM.μ_smul, c.ω_hom_inv]
  exact (P.mul_incl x _).symm

omit [G.IsCocontinuous K J] in
/-- `inclVia` commutes with restriction along a morphism `V ⟶ W`. -/
theorem inclVia_naturality {c : RingComparison (G := G) a a'} (cM : ModuleComparison c.ω M M')
    (P : AlgebraExtension a M) {V W : Dᵒᵖ} (f : V ⟶ W) (m : M'.val.obj V) :
    inclVia cM P W (M'.val.map f m) = P.extension.obj.map (G.op.map f) (inclVia cM P V m) := by
  unfold inclVia
  rw [cM.μ_naturality, P.incl_naturality]

/-- **The restriction of an extension along `G`, read through comparisons of the base data**:
the extension `0 ⟶ ℳ' ⟶ G^*𝒪' ⟶ 𝒪' ⟶ 0` of `𝒜'`-algebras. -/
noncomputable def restrictVia (c : RingComparison (G := G) a a') (cM : ModuleComparison c.ω M M')
    (P : AlgebraExtension a M) : AlgebraExtension a' M' where
  extension := (ringRes K G).obj P.extension
  reduction := (ringRes K G).map P.reduction ≫ c.ω.inv
  locallySurjective := by
    have := P.locallySurjective
    have : Presheaf.IsLocallySurjective K ((ringRes K G).map P.reduction).hom :=
      Presheaf.isLocallySurjective_whisker K J G P.reduction.hom
    have : IsIso c.ω.inv.hom := (inferInstance : IsIso ((sheafToPresheaf K _).map c.ω.inv))
    exact Presheaf.isLocallySurjective_comp K _ _
  squareZero V := by
    have hinj : Function.Injective (c.ω.inv.hom.app V).hom := fun y z h => by
      rw [← c.ω_hom_inv V y, ← c.ω_hom_inv V z]
      exact congrArg (c.ω.hom.hom.app V) h
    have : RingHom.ker (((ringRes K G).map P.reduction ≫ c.ω.inv).hom.app V).hom =
        RingHom.ker (P.reduction.hom.app (G.op.obj V)).hom :=
      RingHom.ker_comp_of_injective (P.reduction.hom.app (G.op.obj V)).hom hinj
    rw [this]
    exact P.squareZero (G.op.obj V)
  algebraMap := c.α.hom ≫ (ringRes K G).map P.algebraMap
  algebraMap_reduction := by
    rw [Category.assoc, ← Category.assoc ((ringRes K G).map P.algebraMap), ← Functor.map_comp,
      P.algebraMap_reduction, ← Category.assoc, ← c.comm, Category.assoc, Iso.hom_inv_id,
      Category.comp_id]
  kernelInclusion :=
    { val :=
      { app := fun V => ModuleCat.ofHom
          (X := ((SheafOfModules.restrictScalars
            ((sheafCompose K (forget₂ CommRingCat.{u} RingCat.{u})).map
              ((ringRes K G).map P.reduction ≫ c.ω.inv))).obj M').val.obj V)
          (Y := (SheafOfModules.unit ((sheafCompose K (forget₂ CommRingCat.{u} RingCat.{u})).obj
              ((ringRes K G).obj P.extension))).val.obj V)
          { toFun := inclVia cM P V
            map_add' := inclVia_add cM P V
            map_smul' := inclVia_smul cM P V }
        naturality := fun {V W} f => by
          ext m
          exact inclVia_naturality cM P f m } }
  kernelZero V m := by
    change c.ω.inv.hom.app V (P.reduction.hom.app (G.op.obj V) (P.incl (cM.μ V m))) = 0
    exact (congrArg (c.ω.inv.hom.app V) (P.reduction_incl (cM.μ V m))).trans (map_zero _)
  kernelUniversal V x hx := by
    have hx' : P.reduction.hom.app (G.op.obj V) x = 0 := by
      rw [← c.ω_hom_inv V (P.reduction.hom.app (G.op.obj V) x)]
      exact (congrArg (c.ω.hom.hom.app V) hx).trans (map_zero _)
    obtain ⟨m, hm, hu⟩ := P.kernelUniversal (G.op.obj V) x hx'
    refine ⟨(cM.μ V).symm m, ?_, fun m' hm' => ?_⟩
    · change P.incl (cM.μ V ((cM.μ V).symm m)) = x
      rw [AddEquiv.apply_symm_apply]
      exact hm
    · rw [AddEquiv.eq_symm_apply]
      exact hu _ hm'

/-- The inclusion of the ideal of `restrictVia c cM P` sends `m` to `ι(μ m)`. -/
theorem restrictVia_incl (c : RingComparison (G := G) a a') (cM : ModuleComparison c.ω M M')
    (P : AlgebraExtension a M) {V : Dᵒᵖ} (m : M'.val.obj V) :
    (P.restrictVia c cM).incl m = P.incl (cM.μ V m) :=
  rfl

/-- The restriction of a morphism of extensions along `φ` to one along `φ'`, for a map `φ'` of
the compared modules matching `φ`. -/
noncomputable def MapAlong.restrictVia (c : RingComparison (G := G) a a')
    (cM : ModuleComparison c.ω M M') (cN : ModuleComparison c.ω N N') {φ : M ⟶ N}
    {φ' : M' ⟶ N'} (hφ : ∀ (V : Dᵒᵖ) (m : M'.val.obj V),
      cN.μ V (φ'.val.app V m) = φ.val.app (G.op.obj V) (cM.μ V m))
    {P : AlgebraExtension a M} {Q : AlgebraExtension a N} (f : MapAlong φ P Q) :
    MapAlong φ' (P.restrictVia c cM) (Q.restrictVia c cN) where
  hom := (ringRes K G).map f.hom
  reduction_comm := by
    change (ringRes K G).map f.hom ≫ (ringRes K G).map Q.reduction ≫ c.ω.inv =
      (ringRes K G).map P.reduction ≫ c.ω.inv
    rw [← Category.assoc, ← Functor.map_comp, f.reduction_comm]
  algebraMap_comm := by
    change (c.α.hom ≫ (ringRes K G).map P.algebraMap) ≫ (ringRes K G).map f.hom =
      c.α.hom ≫ (ringRes K G).map Q.algebraMap
    rw [Category.assoc, ← Functor.map_comp, f.algebraMap_comm]
  kernel_comm V m := by
    change f.hom.hom.app (G.op.obj V) (P.incl (cM.μ V m)) = Q.incl (cN.μ V (φ'.val.app V m))
    rw [f.kernel_comm, hφ]

variable (a' M') in
/-- **Restriction along `G` through comparisons of the base data, as a functor.** -/
noncomputable def restrictViaFunctor (c : RingComparison (G := G) a a')
    (cM : ModuleComparison c.ω M M') : AlgebraExtension a M ⥤ AlgebraExtension a' M' where
  obj P := P.restrictVia c cM
  map f := MapAlong.restrictVia c cM cM (fun _ _ => rfl) f
  map_id P := MapAlong.ext ((ringRes K G).map_id P.extension)
  map_comp f g := MapAlong.ext ((ringRes K G).map_comp f.hom g.hom)

/-- The map of middle terms of the restriction of `f` is the restriction of the map of middle
terms of `f`. -/
@[simp]
theorem restrictViaFunctor_map_hom (c : RingComparison (G := G) a a')
    (cM : ModuleComparison c.ω M M') {P Q : AlgebraExtension a M} (f : P ⟶ Q) :
    ((restrictViaFunctor a' M' c cM).map f).hom = (ringRes K G).map f.hom :=
  rfl

section FullyFaithful

variable [G.IsDenseSubsite K J] (c : RingComparison (G := G) a a')
  (cM : ModuleComparison c.ω M M')

/-- Restriction along a dense subsite is faithful. -/
instance faithful_restrictViaFunctor : (restrictViaFunctor a' M' c cM).Faithful where
  map_injective {_ _} _ _ h := MapAlong.ext ((ringRes K G).map_injective (congrArg MapAlong.hom h))

/-- A homomorphism of middle terms inducing `φ` on ideals over the objects `G(V)` induces `φ` on
ideals everywhere, when every object is isomorphic to some `G(V)`. -/
theorem kernel_comm_of_restrict [G.EssSurj] {φ : M ⟶ N} {P : AlgebraExtension a M}
    {Q : AlgebraExtension a N} (h : P.extension ⟶ Q.extension)
    (hG : ∀ (V : Dᵒᵖ) (m : M.val.obj (G.op.obj V)),
      h.hom.app (G.op.obj V) (P.incl m) = Q.incl (φ.val.app (G.op.obj V) m))
    (U : Cᵒᵖ) (m : M.val.obj U) : h.hom.app U (P.incl m) = Q.incl (φ.val.app U m) := by
  let i : G.obj (G.objPreimage U.unop) ≅ U.unop := G.objObjPreimageIso U.unop
  have hinj : Function.Injective (Q.extension.obj.map i.hom.op) := fun x y hxy => by
    have key : ∀ z : Q.extension.obj.obj U,
        Q.extension.obj.map i.inv.op (Q.extension.obj.map i.hom.op z) = z := fun z => by
      rw [← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp, i.inv_hom_id, op_id,
        CategoryTheory.Functor.map_id]
      rfl
    rw [← key x, ← key y, hxy]
  apply hinj
  rw [← NatTrans.naturality_apply h.hom i.hom.op, ← P.incl_naturality, ← Q.incl_naturality,
    ← PresheafOfModules.naturality_apply φ.val i.hom.op m]
  exact hG (op (G.objPreimage U.unop)) _

variable {N' : SheafOfModules.{u} ((sheafCompose K (forget₂ CommRingCat.{u} RingCat.{u})).obj O')}
  {c} in
/-- **Every morphism along `φ'` of restricted extensions is the restriction of a morphism along
`φ`**, when `G` is a dense subsite whose objects reach every object up to isomorphism. -/
theorem MapAlong.exists_restrictVia_eq [G.EssSurj] (cN : ModuleComparison c.ω N N')
    {φ : M ⟶ N} {φ' : M' ⟶ N'} (hφ : ∀ (V : Dᵒᵖ) (m : M'.val.obj V),
      cN.μ V (φ'.val.app V m) = φ.val.app (G.op.obj V) (cM.μ V m))
    {P : AlgebraExtension a M} {Q : AlgebraExtension a N}
    (g : MapAlong φ' (P.restrictVia c cM) (Q.restrictVia c cN)) :
    ∃ f : MapAlong φ P Q, (ringRes K G).map f.hom = g.hom := by
  obtain ⟨h, hh⟩ := (ringRes K G).map_surjective g.hom
  refine ⟨{ hom := h, reduction_comm := ?_, algebraMap_comm := ?_, kernel_comm := ?_ }, hh⟩
  · apply (ringRes K G).map_injective
    rw [Functor.map_comp, hh]
    exact (cancel_mono c.ω.inv).1 ((Category.assoc _ _ _).trans g.reduction_comm)
  · apply (ringRes K G).map_injective
    rw [Functor.map_comp, hh]
    exact (cancel_epi c.α.hom).1 ((Category.assoc _ _ _).symm.trans g.algebraMap_comm)
  · refine kernel_comm_of_restrict (G := G) h (fun V m => ?_)
    have h1 := g.kernel_comm V ((cM.μ V).symm m)
    rw [← hh] at h1
    change h.hom.app (G.op.obj V) (P.incl (cM.μ V ((cM.μ V).symm m))) =
      Q.incl (cN.μ V (φ'.val.app V ((cM.μ V).symm m))) at h1
    rw [AddEquiv.apply_symm_apply, hφ, AddEquiv.apply_symm_apply] at h1
    exact h1

/-- Restriction along an essentially surjective dense subsite is full. -/
instance full_restrictViaFunctor [G.EssSurj] : (restrictViaFunctor a' M' c cM).Full where
  map_surjective {P Q} g := by
    obtain ⟨f, hf⟩ := MapAlong.exists_restrictVia_eq (φ := 𝟙 M) cM cM (fun _ _ => rfl) g
    exact ⟨f, MapAlong.ext hf⟩

end FullyFaithful

end Restrict

section IsIso

variable {C : Type v₁} [Category.{w₁} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})] {A O : Sheaf J CommRingCat.{u}}
  {a : A ⟶ O}
  {M : SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj O)}

/-- **A morphism of extensions whose map of middle terms is an isomorphism is an isomorphism.** -/
theorem isIso_of_isIso_hom {P Q : AlgebraExtension a M} (f : P ⟶ Q) [IsIso f.hom] : IsIso f := by
  have hinv : ∀ (U : Cᵒᵖ) (y : Q.extension.obj.obj U),
      f.hom.hom.app U ((inv f.hom).hom.app U y) = y := fun U y =>
    congrArg (fun k : Q.extension ⟶ Q.extension => k.hom.app U y) (IsIso.inv_hom_id f.hom)
  let g : Q ⟶ P :=
    { hom := inv f.hom
      reduction_comm := by rw [IsIso.inv_comp_eq, f.reduction_comm]
      algebraMap_comm := by rw [IsIso.comp_inv_eq, f.algebraMap_comm]
      kernel_comm := fun U m => by
        have hf : Function.Injective (f.hom.hom.app U) := fun x y hxy => by
          have := congrArg ((inv f.hom).hom.app U) hxy
          have hl : ∀ x, (inv f.hom).hom.app U (f.hom.hom.app U x) = x := fun x =>
            congrArg (fun k : P.extension ⟶ P.extension => k.hom.app U x) (IsIso.hom_inv_id f.hom)
          rwa [hl, hl] at this
        apply hf
        rw [hinv, f.kernel_comm]
        rfl }
  exact ⟨g, MapAlong.ext (IsIso.hom_inv_id f.hom), MapAlong.ext (IsIso.inv_hom_id f.hom)⟩

end IsIso

end Deformation.AlgebraExtension

end
