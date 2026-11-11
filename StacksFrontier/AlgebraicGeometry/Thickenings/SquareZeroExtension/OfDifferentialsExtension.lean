module

public import StacksFrontier.AlgebraicGeometry.Thickenings.SquareZeroExtension.Realization
public import StacksFrontier.AlgebraicGeometry.Morphisms.Differentials.Relative
public import StacksFrontier.Topology.Sheaves.Modules.SquareZeroExtension
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.EpiImageSubsheaf

/-!
# The square-zero extension attached to an extension of the sheaf of differentials

Let `f : X ⟶ S` be a morphism of schemes and let `0 ⟶ 𝓜 ⟶ 𝓔 ⟶ Ω_{X/S} ⟶ 0` be a short exact
sequence of `𝒪_X`-modules with `𝓜` quasi-coherent. The fibre product
`𝒪' = 𝒪_X ×_{Ω_{X/S}} 𝓔` of the universal derivation `d : 𝒪_X ⟶ Ω_{X/S}` and of `p : 𝓔 ⟶ Ω_{X/S}`
is a sheaf of commutative rings, with multiplication `(a, e) (b, e') = (a b, a e' + b e)`: the
Leibniz rule for `d` and the linearity of `p` are what make the product stay in the fibre
product. The first projection `𝒪' ⟶ 𝒪_X` is a square-zero extension of `𝒪_X` by `𝓜`, embedded
as `m ↦ (0, m)`, and it is an `f⁻¹𝒪_S`-algebra through `r ↦ (f^♯ r, 0)`, since `d` kills
`f^♯ r`.

This is the classical construction realizing a class of `Ext¹(Ω_{X/S}, 𝓜)` by a first-order
thickening of `X` over `S`.

## Main definitions

* `Stacks.Thickenings.DifferentialsExtension.fiberSheaf`: for a sheaf of commutative rings `O`, a
  derivation `δ` of `O` with values in `Ω` and a morphism `p : E ⟶ Ω`, the subsheaf of rings of
  `O ⋉ E` of sections `(a, e)` with `δ a = p e`.
* `Stacks.Thickenings.differentialsSquareZeroExtension`: the square-zero extension of `𝒪_X` over
  `S` attached to a short exact sequence `0 ⟶ 𝓜 ⟶ 𝓔 ⟶ Ω_{X/S} ⟶ 0`.

## References

* [Stacks Project, Tag 05YV](https://stacks.math.columbia.edu/tag/05YV)
* [Stacks Project, Tag 08UB](https://stacks.math.columbia.edu/tag/08UB)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open AlgebraicGeometry.SheafOfModules

universe u

namespace Stacks.Thickenings.DifferentialsExtension

attribute [local instance] Stacks.Smooth.moduleMulOpposite

section Generic

variable {Z : TopCat.{u}} {O₀ O : TopCat.Sheaf CommRingCat.{u} Z}
  {E Ω : _root_.SheafOfModules.{u} (AlgebraicGeometry.SheafOfModules.underlyingRingSheaf O)}
  {φ : O₀ ⟶ O}
  (δ : PresheafOfModulesOfCommRing.Derivation' Ω.val φ.hom) (p : E ⟶ Ω)

/-- The sections `(a, e)` of `O ⋉ E` over `V` with `δ a = p e` form a subring. -/
def fiberSubring (V : (Opens Z)ᵒᵖ) : Subring (TrivSqZeroExt ↥(O.obj.obj V) ↥(E.val.obj V)) where
  carrier := {x | δ.d x.fst = (p.val.app V).hom x.snd}
  mul_mem' {x y} hx hy := by
    have hx' : δ.d x.fst = (p.val.app V).hom x.snd := hx
    have hy' : δ.d y.fst = (p.val.app V).hom y.snd := hy
    change δ.d (x * y).fst = (p.val.app V).hom (x * y).snd
    rw [TrivSqZeroExt.fst_mul, TrivSqZeroExt.snd_mul, δ.d_mul, hx', hy', map_add]
    exact congrArg₂ (· + ·) ((p.val.app V).hom.map_smul x.fst y.snd).symm
      ((p.val.app V).hom.map_smul y.fst x.snd).symm
  one_mem' := by
    change δ.d (1 : TrivSqZeroExt ↥(O.obj.obj V) ↥(E.val.obj V)).fst =
      (p.val.app V).hom (1 : TrivSqZeroExt ↥(O.obj.obj V) ↥(E.val.obj V)).snd
    rw [TrivSqZeroExt.fst_one, TrivSqZeroExt.snd_one, map_zero]
    exact δ.d_one V
  add_mem' {x y} hx hy := by
    have hx' : δ.d x.fst = (p.val.app V).hom x.snd := hx
    have hy' : δ.d y.fst = (p.val.app V).hom y.snd := hy
    change δ.d (x + y).fst = (p.val.app V).hom (x + y).snd
    rw [TrivSqZeroExt.fst_add, TrivSqZeroExt.snd_add, map_add, map_add, hx', hy']
  zero_mem' := by
    change δ.d (0 : TrivSqZeroExt ↥(O.obj.obj V) ↥(E.val.obj V)).fst =
      (p.val.app V).hom (0 : TrivSqZeroExt ↥(O.obj.obj V) ↥(E.val.obj V)).snd
    rw [TrivSqZeroExt.fst_zero, TrivSqZeroExt.snd_zero, map_zero, map_zero]
  neg_mem' {x} hx := by
    have hx' : δ.d x.fst = (p.val.app V).hom x.snd := hx
    change δ.d (-x).fst = (p.val.app V).hom (-x).snd
    rw [TrivSqZeroExt.fst_neg, TrivSqZeroExt.snd_neg, map_neg, map_neg, hx']

/-- Membership in the fibre subring. -/
theorem mem_fiberSubring {V : (Opens Z)ᵒᵖ} {x : TrivSqZeroExt ↥(O.obj.obj V) ↥(E.val.obj V)} :
    x ∈ fiberSubring δ p V ↔ δ.d x.fst = (p.val.app V).hom x.snd :=
  Iff.rfl

/-- Restriction in `O ⋉ E` preserves the fibre subring. -/
theorem map_mem_fiberSubring {V V' : (Opens Z)ᵒᵖ} (h : V ⟶ V')
    {x : TrivSqZeroExt ↥(O.obj.obj V) ↥(E.val.obj V)} (hx : x ∈ fiberSubring δ p V) :
    ((sqZeroPresheaf O E).map h).hom x ∈ fiberSubring δ p V' := by
  refine (mem_fiberSubring δ p).2 ?_
  refine (congrArg δ.d (sqZeroPresheaf_map_fst O E h x)).trans ?_
  refine (δ.d_map h x.fst).trans ?_
  refine (congrArg (Ω.val.map h) ((mem_fiberSubring δ p).1 hx)).trans ?_
  refine (PresheafOfModules.naturality_apply p.val h x.snd).symm.trans ?_
  exact congrArg (p.val.app V').hom (sqZeroPresheaf_map_snd O E h x).symm

/-- The presheaf of commutative rings `V ↦ {(a, e) ∈ O(V) ⋉ E(V) | δ a = p e}`. -/
def fiberPresheaf : (Opens Z)ᵒᵖ ⥤ CommRingCat.{u} where
  obj V := CommRingCat.of (fiberSubring δ p V)
  map h := CommRingCat.ofHom (((sqZeroPresheaf O E).map h).hom.restrict _ _
    fun _ hx => map_mem_fiberSubring δ p h hx)
  map_id V := CommRingCat.hom_ext (RingHom.ext fun x => Subtype.ext
    (congrArg (fun g => g.hom x.1) ((sqZeroPresheaf O E).map_id V)))
  map_comp h h' := CommRingCat.hom_ext (RingHom.ext fun x => Subtype.ext
    (congrArg (fun g => g.hom x.1) ((sqZeroPresheaf O E).map_comp h h')))

/-- A section of `fiberPresheaf` restricts as its underlying section of `O ⋉ E`. -/
theorem fiberPresheaf_map_val {V V' : (Opens Z)ᵒᵖ} (h : V ⟶ V') (x : (fiberPresheaf δ p).obj V) :
    (((fiberPresheaf δ p).map h).hom x).1 = ((sqZeroPresheaf O E).map h).hom x.1 :=
  rfl

/-- **The fibre product `O ×_Ω E` is a sheaf.** A compatible family glues in the sheaf `O ⋉ E`,
and the glued section satisfies `δ a = p e` because both sides are sections of the sheaf `Ω`
which agree on a cover. -/
theorem fiberPresheaf_isSheaf : TopCat.Presheaf.IsSheaf (fiberPresheaf δ p) := by
  rw [TopCat.Presheaf.isSheaf_iff_isSheafUniqueGluing]
  intro ι W sf hsf
  have hsf' : TopCat.Presheaf.IsCompatible (sqZeroPresheaf O E) W (fun i => (sf i).1) :=
    fun i j => congrArg Subtype.val (hsf i j)
  obtain ⟨s, hs, huniq⟩ :=
    (sqZeroPresheaf_isSheaf O E).isSheafUniqueGluing W (fun i => (sf i).1) hsf'
  have hmem : δ.d s.fst = (p.val.app _).hom s.snd := by
    refine TopCat.Presheaf.IsSheaf.section_ext Ω.isSheaf ?_
    intro x hx
    obtain ⟨i, hi⟩ := Opens.mem_iSup.mp hx
    refine ⟨W i, le_iSup W i, hi, ?_⟩
    have h1 := δ.d_map (homOfLE (le_iSup W i)).op s.fst
    have hfst := congrArg TrivSqZeroExt.fst (hs i)
    have hsnd := congrArg TrivSqZeroExt.snd (hs i)
    rw [sqZeroPresheaf_map_fst] at hfst
    rw [sqZeroPresheaf_map_snd, sectionRestrict_apply] at hsnd
    have h2 := PresheafOfModules.naturality_apply p.val (homOfLE (le_iSup W i)).op s.snd
    have h3 : δ.d (sf i).1.fst = (p.val.app _).hom (sf i).1.snd := (sf i).2
    refine h1.symm.trans ?_
    refine (congrArg δ.d hfst).trans ?_
    refine h3.trans ?_
    exact (congrArg (p.val.app _).hom hsnd.symm).trans h2
  exact ⟨⟨s, hmem⟩, fun i => Subtype.ext (hs i),
    fun t ht => Subtype.ext (huniq t.1 fun i => congrArg Subtype.val (ht i))⟩

/-- The fibre product `O ×_Ω E` of `δ` and `p`, as a sheaf of commutative rings. -/
def fiberSheaf : TopCat.Sheaf CommRingCat.{u} Z :=
  ⟨fiberPresheaf δ p, fiberPresheaf_isSheaf δ p⟩

/-- The first projection `O ×_Ω E ⟶ O`. -/
def fiberFst : fiberSheaf δ p ⟶ O :=
  ObjectProperty.homMk
    { app V := CommRingCat.ofHom
        ((TrivSqZeroExt.fstHom ↥(O.obj.obj V) ↥(O.obj.obj V) ↥(E.val.obj V)).toRingHom.comp
          (fiberSubring δ p V).subtype)
      naturality := fun _ _ h => CommRingCat.hom_ext (RingHom.ext fun x =>
        sqZeroPresheaf_map_fst O E h x.1) }

/-- The first projection takes a section to its first component. -/
theorem fiberFst_app_apply (V : (Opens Z)ᵒᵖ) (x : (fiberSheaf δ p).obj.obj V) :
    ((fiberFst δ p).hom.app V).hom x = x.1.fst :=
  rfl

end Generic

section Exactness

variable {C : Type*} [Category C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u}}
  [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [J.HasSheafCompose (forget₂ RingCat.{u} AddCommGrpCat.{u})]

omit [J.HasSheafCompose (forget₂ RingCat.{u} AddCommGrpCat.{u})] in
/-- **Sections of a short exact sequence of sheaves of modules are left exact**: a section of the
middle term killed by the second map is the image of a unique section of the first term. -/
theorem existsUnique_app_eq_of_shortExact {T : ShortComplex (_root_.SheafOfModules.{u} R)}
    (hT : T.ShortExact) (V : Cᵒᵖ) (y : T.X₂.val.obj V) (hy : (T.g.val.app V).hom y = 0) :
    ∃! x : T.X₁.val.obj V, (T.f.val.app V).hom x = y := by
  have key := (Functor.preservesFiniteLimits_iff_forall_exact_map_and_mono
    (_root_.SheafOfModules.forget R ⋙ PresheafOfModules.evaluation R.obj V)).mp inferInstance T hT
  obtain ⟨x, hx⟩ := (ShortComplex.moduleCat_exact_iff _).mp key.1 y hy
  have hinj : Function.Injective (T.f.val.app V).hom :=
    (ModuleCat.mono_iff_injective _).mp key.2
  exact ⟨x, hx, fun x' hx' => hinj (hx'.trans hx.symm)⟩

end Exactness

section Scheme

variable {X S : Scheme.{u}} (f : X ⟶ S) {M E : X.Modules} (j : M ⟶ E)
  (p : E ⟶ Scheme.Hom.relativeDifferentials f)

/-- The sections of an `𝒪_X`-module over `V` form a module over the commutative ring
`𝒪_X(V)`, spelled through `X.sheaf`, as in `Stacks.Thickenings.DifferentialsExtension.fiberSubring`.
-/
local instance moduleSectionsScheme (N : X.Modules) (V : (Opens X)ᵒᵖ) :
    Module ↥(X.sheaf.obj.obj V) ↥(N.val.obj V) :=
  (N.val.obj V).isModule

/-- The sheaf of rings `𝒪_X ×_{Ω_{X/S}} 𝓔` of pairs `(a, e)` with `d a = p e`. -/
abbrev extensionSheaf : TopCat.Sheaf CommRingCat.{u} X :=
  fiberSheaf (Scheme.Hom.universalRelativeDerivation f) p

/-- A section of `𝒪_S` goes to `(f^♯ r, 0)`, which lies in the fibre product since `d` kills
`f^♯ r`. -/
theorem inl_app_mem_fiberSubring (W : S.Opens) (r : Γ(S, W)) :
    (TrivSqZeroExt.inl ((f.app W).hom r) :
        TrivSqZeroExt ↥(X.sheaf.obj.obj (op (f ⁻¹ᵁ W))) ↥(E.val.obj (op (f ⁻¹ᵁ W)))) ∈
      fiberSubring (Scheme.Hom.universalRelativeDerivation f) p (op (f ⁻¹ᵁ W)) :=
  (mem_fiberSubring _ _).2 ((Scheme.Hom.universalRelativeDerivation_d_app_eq_zero f W r).trans
    (map_zero (p.val.app (op (f ⁻¹ᵁ W))).hom).symm)

/-- The structure map `𝒪_S ⟶ f_*(𝒪_X ×_Ω 𝓔)`, `r ↦ (f^♯ r, 0)`. -/
def extensionToBaseC :
    S.presheaf ⟶ (TopCat.Presheaf.pushforward CommRingCat.{u} f.base).obj
      (extensionSheaf f p).obj where
  app W := CommRingCat.ofHom (((TrivSqZeroExt.inlHom ↥(X.sheaf.obj.obj (op (f ⁻¹ᵁ W.unop)))
    ↥(E.val.obj (op (f ⁻¹ᵁ W.unop)))).comp (f.app W.unop).hom).codRestrict
    _ fun r => inl_app_mem_fiberSubring f p W.unop r)
  naturality W W' g := by
    ext r
    refine Subtype.ext (TrivSqZeroExt.ext ?_ ?_)
    · exact (congrArg (fun φ => φ.hom r) (f.c.naturality g)).trans
        (sqZeroPresheaf_map_fst X.sheaf E ((Opens.map f.base).op.map g)
          (TrivSqZeroExt.inl ((f.app W.unop).hom r))).symm
    · exact (map_zero (sectionRestrict E ((Opens.map f.base).op.map g))).symm.trans
        (sqZeroPresheaf_map_snd X.sheaf E ((Opens.map f.base).op.map g)
          (TrivSqZeroExt.inl ((f.app W.unop).hom r))).symm

/-- The inclusion of `X` into the ringed space `(|X|, 𝒪_X ×_Ω 𝓔)`, given by the first
projection. -/
def extensionInclusion : X.toSheafedSpace ⟶ thickenedSpace X (extensionSheaf f p) :=
  InducedCategory.homMk
    { base := 𝟙 (X : TopCat), c := (fiberFst (Scheme.Hom.universalRelativeDerivation f) p).hom }

/-- The structure morphism of `(|X|, 𝒪_X ×_Ω 𝓔)` to `S`. -/
def extensionToBase : thickenedSpace X (extensionSheaf f p) ⟶ S.toSheafedSpace :=
  InducedCategory.homMk { base := f.base, c := extensionToBaseC f p }

/-- The inclusion followed by the structure morphism is `f`. -/
theorem extensionInclusion_comp_toBase :
    extensionInclusion f p ≫ extensionToBase f p = f.toLRSHom.toShHom := by
  refine InducedCategory.hom_ext (PresheafedSpace.hext _ _ rfl (heq_of_eq ?_))
  exact NatTrans.ext (funext fun W => CommRingCat.hom_ext (RingHom.ext fun r => rfl))

variable {f j p}

/-- The kernel `𝓜 ⟶ 𝒪_X ×_Ω 𝓔`, `m ↦ (0, j m)`. -/
def extensionKernelInclusion (w : j ≫ p = 0) (U : (Opens X)ᵒᵖ) :
    M.val.obj U →+ (extensionSheaf f p).presheaf.obj U where
  toFun m := ⟨TrivSqZeroExt.inr ((j.val.app U).hom m), by
    change (Scheme.Hom.universalRelativeDerivation f).d 0 = (p.val.app U).hom ((j.val.app U).hom m)
    rw [map_zero]
    exact (congrArg (fun φ : M ⟶ _ => (φ.val.app U).hom m) w).symm⟩
  map_zero' := Subtype.ext (TrivSqZeroExt.ext rfl (map_zero (j.val.app U).hom))
  map_add' a b := Subtype.ext (TrivSqZeroExt.ext (add_zero 0).symm (map_add (j.val.app U).hom a b))

variable (f p) in
/-- **The first projection `𝒪_X ×_Ω 𝓔 ⟶ 𝒪_X` is locally surjective** when `p` is an
epimorphism: `d a` lifts locally along `p`, and a local lift `e` gives the section `(a, e)`. -/
theorem isLocallySurjective_fiberFst [Epi p] :
    TopCat.Presheaf.IsLocallySurjective
      (fiberFst (Scheme.Hom.universalRelativeDerivation f) p).hom := by
  have : Epi (C := _root_.SheafOfModules.{u} X.ringCatSheaf) p := ‹Epi p›
  have hp := (TopCat.Presheaf.isLocallySurjective_iff _).1
    (Stacks.SheafOfModules.ImageSubsheaf.isLocallySurjective_of_epi (R := X.ringCatSheaf)
      (M := E) (N := Scheme.Hom.relativeDifferentials f) p)
  rw [TopCat.Presheaf.isLocallySurjective_iff]
  intro U a x hx
  obtain ⟨V, hVU, ⟨e, he⟩, hxV⟩ := hp U ((Scheme.Hom.universalRelativeDerivation f).d a) x hx
  refine ⟨V, hVU, ⟨⟨((X.presheaf.map (homOfLE hVU).op).hom a, e), ?_⟩, rfl⟩, hxV⟩
  exact ((Scheme.Hom.universalRelativeDerivation f).d_map (homOfLE hVU).op a).trans he.symm

/-- Multiplication in `𝒪_X ×_Ω 𝓔`, read on second components: the Leibniz rule
`(a, e) (b, e') = (a b, a e' + b e)`. -/
theorem extensionSheaf_mul_snd (V : (Opens X)ᵒᵖ) (a b : (extensionSheaf f p).presheaf.obj V) :
    (a * b).1.snd = a.1.fst • b.1.snd + b.1.fst • a.1.snd :=
  TrivSqZeroExt.snd_mul a.1 b.1

/-- Restriction in `𝒪_X ×_Ω 𝓔`, read on second components. -/
theorem extensionSheaf_map_snd {V V' : (Opens X)ᵒᵖ} (g : V ⟶ V')
    (a : (extensionSheaf f p).presheaf.obj V) :
    (((extensionSheaf f p).presheaf.map g).hom a).1.snd = E.val.map g a.1.snd :=
  sqZeroPresheaf_map_snd X.sheaf E g a.1

/-- The kernel inclusion commutes with restriction. -/
theorem extensionKernelInclusion_naturality (w : j ≫ p = 0) {U V : (Opens X)ᵒᵖ} (g : U ⟶ V)
    (x : M.val.obj U) :
    extensionKernelInclusion w V (M.val.map g x) =
      (extensionSheaf f p).presheaf.map g (extensionKernelInclusion w U x) := by
  refine Subtype.ext (TrivSqZeroExt.ext ?_ ?_)
  · exact (map_zero (X.sheaf.obj.map g).hom).symm.trans
      (sqZeroPresheaf_map_fst X.sheaf E g (extensionKernelInclusion w U x).1).symm
  · exact (PresheafOfModules.naturality_apply j.val g x).trans
      (sqZeroPresheaf_map_snd X.sheaf E g (extensionKernelInclusion w U x).1).symm

/-- The image of a section of `𝓜` under the kernel inclusion has vanishing first component. -/
theorem extensionKernelInclusion_mem_kernel (w : j ≫ p = 0) (U : (Opens X)ᵒᵖ) (x : M.val.obj U) :
    ((fiberFst (Scheme.Hom.universalRelativeDerivation f) p).hom.app U).hom
      (extensionKernelInclusion w U x) = 0 :=
  rfl

/-- **The kernel of the first projection is `𝓜`.** A section `(0, e)` has `p e = d 0 = 0`, so
`e = j m` for a unique `m` by left exactness of sections. -/
theorem extensionKernelInclusion_exact (w : j ≫ p = 0) (hT : (ShortComplex.mk j p w).ShortExact)
    (U : (Opens X)ᵒᵖ) (a : (extensionSheaf f p).presheaf.obj U)
    (ha : ((fiberFst (Scheme.Hom.universalRelativeDerivation f) p).hom.app U).hom a = 0) :
    ∃! x, extensionKernelInclusion w U x = a := by
  have ha' : a.1.fst = 0 := ha
  have hpa : (p.val.app U).hom a.1.snd = 0 := by
    rw [← a.2, ha', map_zero]
  obtain ⟨m, hm, huniq⟩ := existsUnique_app_eq_of_shortExact hT U a.1.snd hpa
  refine ⟨m, Subtype.ext (TrivSqZeroExt.ext ha'.symm hm), fun m' hm' => huniq m' ?_⟩
  exact congrArg (fun z : (extensionSheaf f p).presheaf.obj U => z.1.snd) hm'

/-- The module structure of `𝓜` is multiplication by local lifts. -/
theorem extensionKernelInclusion_smul (w : j ≫ p = 0) (U : (Opens X)ᵒᵖ)
    (a : (extensionSheaf f p).presheaf.obj U) (x : M.val.obj U) :
    extensionKernelInclusion w U
        (((M.val.obj U).smul
          (((fiberFst (Scheme.Hom.universalRelativeDerivation f) p).hom.app U).hom a)).asHom.hom
          x) =
      a * extensionKernelInclusion w U x := by
  refine Subtype.ext (TrivSqZeroExt.ext ?_ ?_)
  · change (0 : ↥(X.sheaf.obj.obj U)) = (a.1 * TrivSqZeroExt.inr ((j.val.app U).hom x)).fst
    rw [TrivSqZeroExt.fst_mul, TrivSqZeroExt.fst_inr, mul_zero]
  · change (j.val.app U).hom (((M.val.obj U).smul a.1.fst).asHom.hom x) =
      (a.1 * TrivSqZeroExt.inr ((j.val.app U).hom x)).snd
    refine ((j.val.app U).hom.map_smul a.1.fst x).trans ?_
    rw [TrivSqZeroExt.snd_mul, TrivSqZeroExt.fst_inr, TrivSqZeroExt.snd_inr, MulOpposite.op_zero,
      zero_smul, add_zero]
    rfl

/-- The kernel of the first projection has square zero. -/
theorem extensionKernelInclusion_square_zero (w : j ≫ p = 0) (U : (Opens X)ᵒᵖ)
    (x y : M.val.obj U) :
    extensionKernelInclusion w U x * extensionKernelInclusion w U y = 0 :=
  Subtype.ext (TrivSqZeroExt.inr_mul_inr _ _ _)

variable (f j p) in
/-- **The square-zero extension of `𝒪_X` over `S` attached to an extension
`0 ⟶ 𝓜 ⟶ 𝓔 ⟶ Ω_{X/S} ⟶ 0`**: the fibre product `𝒪_X ×_{Ω_{X/S}} 𝓔`, with kernel `𝓜`. -/
def differentialsSquareZeroExtension [M.IsQuasicoherent] (w : j ≫ p = 0)
    (hT : (ShortComplex.mk j p w).ShortExact) : SquareZeroExtension f where
  A := extensionSheaf f p
  π := fiberFst (Scheme.Hom.universalRelativeDerivation f) p
  locallySurjective_π := by
    have : Epi p := hT.epi_g
    exact isLocallySurjective_fiberFst f p
  inclusion := extensionInclusion f p
  inclusion_base := rfl
  inclusion_sheaf := HEq.rfl
  toBase := extensionToBase f p
  over_base := extensionInclusion_comp_toBase f p
  I := M
  quasicoherent := inferInstance
  ι := extensionKernelInclusion w
  naturality := extensionKernelInclusion_naturality w
  mem_kernel := extensionKernelInclusion_mem_kernel w
  exact_kernel := extensionKernelInclusion_exact w hT
  smul_lift := extensionKernelInclusion_smul w
  square_zero := extensionKernelInclusion_square_zero w

end Scheme

section Thickening

variable {X S : Scheme.{u}} {f : X ⟶ S} {M E : X.Modules} {j : M ⟶ E}
  {p : E ⟶ Scheme.Hom.relativeDifferentials f} [M.IsQuasicoherent] (w : j ≫ p = 0)
  (hT : (ShortComplex.mk j p w).ShortExact)

/-- **The first-order thickening of `X` over `S` attached to `0 ⟶ 𝓜 ⟶ 𝓔 ⟶ Ω_{X/S} ⟶ 0`**: the
scheme `(|X|, 𝒪_X ×_{Ω_{X/S}} 𝓔)` of [Stacks Project, Tag 05YV]. -/
abbrev differentialsThickening : Scheme.{u} :=
  squareZeroExtensionScheme (differentialsSquareZeroExtension f j p w hT)
    fun U hU => squareZero_affineChartToSpec_isIso _ U hU

/-- The closed immersion of `X` into `differentialsThickening`. -/
abbrev differentialsThickeningι : X ⟶ differentialsThickening w hT :=
  squareZeroExtensionImmersion _ _

/-- The structure morphism of `differentialsThickening` to `S`. -/
abbrev differentialsThickeningToBase : differentialsThickening w hT ⟶ S :=
  squareZeroExtensionToBase _ _

/-- The thickening lies over `S`: `X ⟶ X' ⟶ S` is `f`. -/
theorem differentialsThickeningι_comp_toBase :
    differentialsThickeningι w hT ≫ differentialsThickeningToBase w hT = f :=
  squareZeroExtensionImmersion_comp_toBase _ _

instance isClosedImmersion_differentialsThickeningι :
    IsClosedImmersion (differentialsThickeningι w hT) :=
  squareZeroExtensionImmersion_isClosedImmersion _ _

/-- The ideal of `X` in `differentialsThickening` has square zero. -/
theorem differentialsThickeningι_ker_sq : (differentialsThickeningι w hT).ker ^ 2 = ⊥ :=
  squareZeroExtensionImmersion_ker_sq _ _

end Thickening

end Stacks.Thickenings.DifferentialsExtension

end
