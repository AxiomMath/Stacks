module

public import StacksFrontier.CategoryTheory.Sites.InverseSystem.ExtColimitOfFiniteSites
public import StacksFrontier.CategoryTheory.Abelian.ColimitLongExactDescent

/-!
# The `Ext` colimit along a short exact sequence of first variables

Let `D` be an inverse system of sites with finite coverings with colimit site `C`, `F` a system of
abelian sheaves on its levels presenting `𝒢` on `C`, and `𝒜' ⟶ 𝒜 ⟶ 𝒜''` a short exact sequence of
first variables (`Stacks.WeakSites.ExtColimit.FirstVariable`): short exact at every arrow into the
index and on the colimit site, compatibly with the comparison maps and legs. The contravariant long
exact `Ext` sequences

`Ext^n(𝒜''_A, F_A) ⟶ Ext^n(𝒜_A, F_A) ⟶ Ext^n(𝒜'_A, F_A) ⟶ Ext^{n+1}(𝒜''_A, F_A) ⟶ ⋯`

are natural in the arrow `A` — the connecting maps commute with `Ext` along the exact inverse
images, which is the naturality of the connecting maps under pullback along the transitions — and
the legs of the `Ext` cocones carry them to the long exact sequence on the colimit site. They form
a `Stacks.Cohomology.ColimitLongExact.Ladder`, so the colimit property of the `Ext` cocones has the
two-out-of-three property along the sequence.

This is the Mayer–Vietoris step of [Stacks, Tag 03Q6]: for a covering `W = U ∪ V` the free sheaves
form a short exact sequence `ℤ[U ∩ V] ⟶ ℤ[U] ⊕ ℤ[V] ⟶ ℤ[W]` of first variables, the colimit
property at `ℤ[U] ⊕ ℤ[V]` follows from `U` and `V` by the split sequence, and that at `ℤ[W]` from
those at `ℤ[U ∩ V]` and `ℤ[U] ⊕ ℤ[V]`; `AlgebraicGeometry.Scheme.Opens.mayerVietoris_induction`
then carries it from affine opens to every quasi-compact open of a quasi-separated scheme.

## Main definitions

* `Stacks.WeakSites.ExtColimit.FirstVariable.Hom` — a morphism of first variables.
* `Stacks.WeakSites.ExtColimit.FirstVariable.ShortExact` — a short exact sequence of them.
* `Stacks.WeakSites.ExtColimit.FirstVariable.ShortExact.ladder` — its `Ext` ladder.
* `Stacks.WeakSites.ExtColimit.FirstVariable.Split` — a first variable split as a direct sum.

## Main results

* `Stacks.WeakSites.ExtColimit.FirstVariable.ShortExact.nonempty_isColimit_right` — the colimit
  property at `𝒜''` from those at `𝒜` and `𝒜'`, in every degree.
* `Stacks.WeakSites.ExtColimit.FirstVariable.ShortExact.nonempty_isColimit_middle` — the colimit
  property at `𝒜` from those at `𝒜'` and `𝒜''`, in every degree.
* `Stacks.WeakSites.ExtColimit.FirstVariable.Split.nonempty_isColimit` — the colimit property at
  a first variable split as `𝒜₁ ⊕ 𝒜₂`, from those at the summands.
* `Stacks.WeakSites.ExtColimit.extTransition_precomp`,
  `Stacks.WeakSites.ExtColimit.extTransition_extClass_comp` — naturality of the maps and the
  connecting maps of the sequence under the transitions.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian Opposite
open CategoryTheory.Sites.InverseSystem

universe v u w t

namespace Stacks.WeakSites.ExtColimit

open InverseSystemOfFiniteSites Stacks.Homology Stacks.WeakSites.ColimitSiteCohomology

variable {D : InverseSystemOfFiniteSites.{v, u, max u v w}}
  {C : Type (max u v w)} [SmallCategory C]
  {uC : ∀ i, D.C i ⥤ C} {hu : ∀ {i j : D.I} (a : i ⟶ j), D.u a ⋙ uC i = uC j}
  {K : Precoverage C} [∀ i, (uC i).IsContinuous (D.J i) K.toGrothendieck]

namespace FirstVariable

variable {i : D.I}

/-- **A morphism of first variables**: maps at every arrow into `i` and on the colimit site,
commuting with the comparison maps and with the legs. -/
structure Hom (𝒜 𝒜' : FirstVariable.{v, u, w} D uC hu K i) where
  /-- The map at an arrow. -/
  app : ∀ A : Over i, 𝒜.obj A ⟶ 𝒜'.obj A
  /-- The map on the colimit site. -/
  top : 𝒜.top ⟶ 𝒜'.top
  comm : ∀ {A B : Over i} (f : A ⟶ B),
    app A ≫ 𝒜'.map f = 𝒜.map f ≫ (pb.{v, u, w} D f.left).map (app B)
  top_comm : ∀ A : Over i,
    top ≫ 𝒜'.leg A = 𝒜.leg A ≫ (colimitPullback.{v, u, w} D uC K A.left).map (app A)

/-- **A short exact sequence of first variables** `𝒜' ⟶ 𝒜 ⟶ 𝒜''`. -/
structure ShortExact (𝒜' 𝒜 𝒜'' : FirstVariable.{v, u, w} D uC hu K i) where
  /-- The first map. -/
  φ : Hom 𝒜' 𝒜
  /-- The second map. -/
  π : Hom 𝒜 𝒜''
  /-- The composite of the two maps vanishes at every arrow. -/
  w : ∀ A, φ.app A ≫ π.app A = 0
  /-- The composite of the two maps vanishes on the colimit site. -/
  w_top : φ.top ≫ π.top = 0
  /-- The sequence is short exact at every arrow. -/
  shortExact : ∀ A, (ShortComplex.mk _ _ (w A)).ShortExact
  /-- The sequence is short exact on the colimit site. -/
  shortExact_top : (ShortComplex.mk _ _ w_top).ShortExact

end FirstVariable

variable [∀ j, PreservesFiniteLimits (colimitPullback.{v, u, w} D uC K j)]
  [∀ j, EnoughInjectives (Sheaf (D.J j) Ab.{max u v w})]
  [∀ j, HasExt.{max u v w} (Sheaf (D.J j) Ab.{max u v w})]
  [HasExt.{max u v w} (Sheaf K.toGrothendieck Ab.{max u v w})]

variable {i : D.I} {𝒜 𝒜' : FirstVariable.{v, u, w} D uC hu K i}
  (F : AbelianSheafSystem.{v, u, max u v w, max u v w} D)
  {𝒢 : Sheaf K.toGrothendieck Ab.{max u v w}} (ι : ∀ j, (F.obj j).obj ⟶ (uC j).op ⋙ 𝒢.obj)
  (n : ℕ)

omit [∀ j, PreservesFiniteLimits (colimitPullback.{v, u, w} D uC K j)]
  [∀ j, EnoughInjectives (Sheaf (D.J j) Ab.{max u v w})]
  [HasExt.{max u v w} (Sheaf K.toGrothendieck Ab.{max u v w})] in
/-- Precomposition with the degree-zero class of `a : X' ⟶ X` is `extConj a (𝟙 Y)`. -/
theorem mk₀_comp_eq_extConj {X' X Y : Sheaf (D.J i) Ab.{max u v w}} (a : X' ⟶ X)
    (x : Ext.{max u v w} X Y n) : (Ext.mk₀ a).comp x (zero_add n) = extConj a (𝟙 Y) x := by
  simp [extConj]

omit [∀ j, PreservesFiniteLimits (colimitPullback.{v, u, w} D uC K j)]
  [∀ j, EnoughInjectives (Sheaf (D.J j) Ab.{max u v w})]
  [HasExt.{max u v w} (Sheaf K.toGrothendieck Ab.{max u v w})] in
/-- **The transitions of the `Ext` diagram commute with precomposition** by a morphism of first
variables. -/
theorem extTransition_precomp (h : FirstVariable.Hom 𝒜 𝒜') {A B : Over i} (f : A ⟶ B)
    (x : Ext.{max u v w} (𝒜'.obj B) (F.obj B.left) n) :
    extTransition 𝒜 F n f ((Ext.mk₀ (h.app B)).comp x (zero_add n)) =
      (Ext.mk₀ (h.app A)).comp (extTransition 𝒜' F n f x) (zero_add n) := by
  rw [extTransition_apply, extTransition_apply, mk₀_comp_eq_extConj, mk₀_comp_eq_extConj,
    extConj_mapExactFunctor, extConj_extConj, extConj_extConj, CategoryTheory.Functor.map_id,
    Category.id_comp, Category.comp_id, h.comm]

omit [∀ j, EnoughInjectives (Sheaf (D.J j) Ab.{max u v w})] in
/-- **The legs of the `Ext` cocone commute with precomposition** by a morphism of first
variables. -/
theorem extLeg_precomp (h : FirstVariable.Hom 𝒜 𝒜') (A : Over i)
    (x : Ext.{max u v w} (𝒜'.obj A) (F.obj A.left) n) :
    extLeg 𝒜 F ι n A ((Ext.mk₀ (h.app A)).comp x (zero_add n)) =
      (Ext.mk₀ h.top).comp (extLeg 𝒜' F ι n A x) (zero_add n) := by
  rw [extLeg_apply, extLeg_apply, mk₀_comp_eq_extConj, extConj_mapExactFunctor, extConj_extConj,
    CategoryTheory.Functor.map_id, Category.id_comp]
  simp only [extConj, Ext.mk₀_comp_mk₀_assoc, h.top_comm]

/-- Naturality of the connecting morphism of short exact sequences, with a degree-zero morphism
precomposed. -/
private theorem mk₀_comp_extClass_comp {𝒞 : Type*} [Category* 𝒞] [Abelian 𝒞] [HasExt.{t} 𝒞]
    {S₁ S₂ : ShortComplex 𝒞} (hS₁ : S₁.ShortExact) (hS₂ : S₂.ShortExact) (τ : S₁ ⟶ S₂)
    {Y : 𝒞} (z : Ext.{t} S₂.X₁ Y n) :
    (Ext.mk₀ τ.τ₃).comp (hS₂.extClass.comp z (add_comm 1 n)) (zero_add _) =
      hS₁.extClass.comp ((Ext.mk₀ τ.τ₁).comp z (zero_add n)) (add_comm 1 n) := by
  rw [← Ext.comp_assoc _ _ _ (zero_add 1) (add_comm 1 n) (by lia),
    ← hS₁.extClass_naturality hS₂ τ, Ext.comp_assoc _ _ _ (add_zero 1) (zero_add n) (by lia)]

variable {𝒜'' : FirstVariable.{v, u, w} D uC hu K i} (S : FirstVariable.ShortExact 𝒜' 𝒜 𝒜'')

omit [∀ j, PreservesFiniteLimits (colimitPullback.{v, u, w} D uC K j)]
  [∀ j, EnoughInjectives (Sheaf (D.J j) Ab.{max u v w})]
  [HasExt.{max u v w} (Sheaf K.toGrothendieck Ab.{max u v w})] in
/-- **The connecting maps commute with the transitions**: the connecting map of the sequence at
`B`, followed by `Ext` along the transition `f⁻¹`, is `Ext` along `f⁻¹` followed by the connecting
map at `A`. This is the naturality of the connecting maps under pullback along the transitions. -/
theorem extTransition_extClass_comp {A B : Over i} (f : A ⟶ B)
    (x : Ext.{max u v w} (𝒜'.obj B) (F.obj B.left) n) :
    extTransition 𝒜'' F (n + 1) f ((S.shortExact B).extClass.comp x (add_comm 1 n)) =
      (S.shortExact A).extClass.comp (extTransition 𝒜' F n f x) (add_comm 1 n) := by
  let τ : ShortComplex.mk _ _ (S.w A) ⟶
      (ShortComplex.mk _ _ (S.w B)).map (pb.{v, u, w} D f.left) :=
    { τ₁ := 𝒜'.map f
      τ₂ := 𝒜.map f
      τ₃ := 𝒜''.map f
      comm₁₂ := (S.φ.comm f).symm
      comm₂₃ := (S.π.comm f).symm }
  rw [extTransition_apply, extTransition_apply, Ext.mapExactFunctor_comp,
    Ext.mapExactFunctor_extClass]
  simp only [extConj, Ext.comp_assoc_of_third_deg_zero]
  exact mk₀_comp_extClass_comp n (S.shortExact A)
    ((S.shortExact B).map_of_exact (pb.{v, u, w} D f.left)) τ _

omit [∀ j, EnoughInjectives (Sheaf (D.J j) Ab.{max u v w})] in
/-- **The legs of the `Ext` cocone commute with the connecting maps.** -/
theorem extLeg_extClass_comp (A : Over i) (x : Ext.{max u v w} (𝒜'.obj A) (F.obj A.left) n) :
    extLeg 𝒜'' F ι (n + 1) A ((S.shortExact A).extClass.comp x (add_comm 1 n)) =
      S.shortExact_top.extClass.comp (extLeg 𝒜' F ι n A x) (add_comm 1 n) := by
  let τ : ShortComplex.mk _ _ S.w_top ⟶
      (ShortComplex.mk _ _ (S.w A)).map (colimitPullback.{v, u, w} D uC K A.left) :=
    { τ₁ := 𝒜'.leg A
      τ₂ := 𝒜.leg A
      τ₃ := 𝒜''.leg A
      comm₁₂ := (S.φ.top_comm A).symm
      comm₂₃ := (S.π.top_comm A).symm }
  rw [extLeg_apply, extLeg_apply, Ext.mapExactFunctor_comp, Ext.mapExactFunctor_extClass]
  simp only [extConj, Ext.comp_assoc_of_third_deg_zero]
  exact mk₀_comp_extClass_comp n S.shortExact_top
    ((S.shortExact A).map_of_exact (colimitPullback.{v, u, w} D uC K A.left)) τ _

/-- Two precompositions with morphisms of degree zero whose composite vanishes give zero. -/
private theorem mk₀_comp_mk₀_comp_eq_zero {𝒞 : Type*} [Category* 𝒞] [Abelian 𝒞] [HasExt.{t} 𝒞]
    {X Y Z W : 𝒞} (a : X ⟶ Y) (b : Y ⟶ Z) (h : a ≫ b = 0) (x : Ext.{t} Z W n) :
    (Ext.mk₀ a).comp ((Ext.mk₀ b).comp x (zero_add n)) (zero_add n) = 0 := by
  rw [Ext.mk₀_comp_mk₀_assoc, h, Ext.mk₀_zero, Ext.zero_comp]

/-- Two precompositions with morphisms of degree zero whose composite is the identity give the
identity. -/
private theorem mk₀_comp_mk₀_comp_eq_self {𝒞 : Type*} [Category* 𝒞] [Abelian 𝒞] [HasExt.{t} 𝒞]
    {X Y W : 𝒞} (a : X ⟶ Y) (b : Y ⟶ X) (h : a ≫ b = 𝟙 X) (x : Ext.{t} X W n) :
    (Ext.mk₀ a).comp ((Ext.mk₀ b).comp x (zero_add n)) (zero_add n) = x := by
  rw [Ext.mk₀_comp_mk₀_assoc, h, Ext.mk₀_id_comp]

/-- A morphism of diagrams and a compatible morphism of vertices commute with the comparisons from
the colimits, checked on elements. -/
private theorem colimMap_desc_comm_apply {I : Type*} [Category* I]
    [HasColimitsOfShape I AddCommGrpCat.{t}] {D D' : I ⥤ AddCommGrpCat.{t}} (a : D ⟶ D')
    (c : Cocone D) (c' : Cocone D') (f : c.pt ⟶ c'.pt)
    (h : ∀ j x, f (c.ι.app j x) = c'.ι.app j (a.app j x)) :
    colim.map a ≫ colimit.desc D' c' = colimit.desc D c ≫ f :=
  Stacks.Cohomology.ColimitLongExact.colimMap_desc_comm a c c' f fun j => by ext x; exact h j x

/-! ### The ladder -/

namespace FirstVariable.ShortExact

/-- Precomposition by a morphism of first variables, as a morphism of `Ext` diagrams. -/
def precompNat (h : FirstVariable.Hom 𝒜 𝒜') : extDiagram 𝒜' F n ⟶ extDiagram 𝒜 F n where
  app A := AddCommGrpCat.ofHom ((Ext.mk₀ (h.app A.unop)).precomp _ (zero_add n))
  naturality A B f := by
    ext x
    exact (extTransition_precomp F n h f.unop x).symm

/-- The connecting map of the sequence, as a morphism of `Ext` diagrams. -/
def deltaNat : extDiagram 𝒜' F n ⟶ extDiagram 𝒜'' F (n + 1) where
  app A := AddCommGrpCat.ofHom ((S.shortExact A.unop).extClass.precomp _ (add_comm 1 n))
  naturality A B f := by
    ext x
    exact (extTransition_extClass_comp F n S f.unop x).symm

variable {F}

omit [∀ j, PreservesFiniteLimits (colimitPullback.{v, u, w} D uC K j)]
  [HasExt.{max u v w} (Sheaf K.toGrothendieck Ab.{max u v w})] in
/-- Precomposition by `π` followed by precomposition by `φ` is zero. -/
theorem w_ab : precompNat F n S.π ≫ precompNat F n S.φ = 0 := by
  ext A x
  exact mk₀_comp_mk₀_comp_eq_zero n _ _ (S.w A.unop) x

omit [∀ j, PreservesFiniteLimits (colimitPullback.{v, u, w} D uC K j)]
  [HasExt.{max u v w} (Sheaf K.toGrothendieck Ab.{max u v w})] in
/-- Precomposition by `φ` followed by the connecting map is zero. -/
theorem w_bδ : precompNat F n S.φ ≫ S.deltaNat F n = 0 := by
  ext A x
  exact ShortComplex.ShortExact.extClass_comp_assoc (S.shortExact A.unop) x (h := add_comm 1 n)

omit [∀ j, PreservesFiniteLimits (colimitPullback.{v, u, w} D uC K j)]
  [HasExt.{max u v w} (Sheaf K.toGrothendieck Ab.{max u v w})] in
/-- The connecting map followed by precomposition by `π` is zero. -/
theorem w_δa : S.deltaNat F n ≫ precompNat F (n + 1) S.π = 0 := by
  ext A x
  exact ShortComplex.ShortExact.comp_extClass_assoc (S.shortExact A.unop) x (add_comm 1 n)

omit [∀ j, PreservesFiniteLimits (colimitPullback.{v, u, w} D uC K j)]
  [HasExt.{max u v w} (Sheaf K.toGrothendieck Ab.{max u v w})] in
/-- The sequence of `Ext` diagrams is exact at the diagram of `𝒜`. -/
theorem exact_ab : (ShortComplex.mk _ _ (S.w_ab (F := F) n)).Exact :=
  Stacks.Cohomology.MayerVietoris.shortComplex_exact_of_pointwise _ fun A =>
    Ext.contravariant_sequence_exact₂' (S.shortExact A.unop) (F.obj A.unop.left) n

omit [∀ j, PreservesFiniteLimits (colimitPullback.{v, u, w} D uC K j)]
  [HasExt.{max u v w} (Sheaf K.toGrothendieck Ab.{max u v w})] in
/-- The sequence of `Ext` diagrams is exact at the diagram of `𝒜'`. -/
theorem exact_bδ : (ShortComplex.mk _ _ (S.w_bδ (F := F) n)).Exact :=
  Stacks.Cohomology.MayerVietoris.shortComplex_exact_of_pointwise _ fun A =>
    Ext.contravariant_sequence_exact₁' (S.shortExact A.unop) (F.obj A.unop.left) n (n + 1)
      (add_comm 1 n)

omit [∀ j, PreservesFiniteLimits (colimitPullback.{v, u, w} D uC K j)]
  [HasExt.{max u v w} (Sheaf K.toGrothendieck Ab.{max u v w})] in
/-- The sequence of `Ext` diagrams is exact at the degree `n + 1` diagram of `𝒜''`. -/
theorem exact_δa : (ShortComplex.mk _ _ (S.w_δa (F := F) n)).Exact :=
  Stacks.Cohomology.MayerVietoris.shortComplex_exact_of_pointwise _ fun A =>
    Ext.contravariant_sequence_exact₃' (S.shortExact A.unop) (F.obj A.unop.left) n (n + 1)
      (add_comm 1 n)

/-- Precomposition by a morphism of first variables on the colimit site, at the vertex. -/
abbrev precompTop (h : FirstVariable.Hom 𝒜 𝒜') :
    AddCommGrpCat.of (Ext.{max u v w} 𝒜'.top 𝒢 n) ⟶ AddCommGrpCat.of (Ext.{max u v w} 𝒜.top 𝒢 n) :=
  AddCommGrpCat.ofHom ((Ext.mk₀ h.top).precomp _ (zero_add n))

variable (𝒢) in
/-- The connecting map of the sequence on the colimit site. -/
abbrev deltaTop :
    AddCommGrpCat.of (Ext.{max u v w} 𝒜'.top 𝒢 n) ⟶
      AddCommGrpCat.of (Ext.{max u v w} 𝒜''.top 𝒢 (n + 1)) :=
  AddCommGrpCat.ofHom (S.shortExact_top.extClass.precomp _ (add_comm 1 n))

variable [HasColimitsOfShape (Over i)ᵒᵖ Ab.{max u v w}]
  (hι : IsCompatible.{v, u, max u v w, max u v w} D uC hu F 𝒢.obj ι)

/-- **The `Ext` ladder of a short exact sequence of first variables**: the contravariant long
exact sequences on the levels and on the colimit site, and the comparisons from the colimits of the
`Ext` diagrams. -/
def ladder : Stacks.Cohomology.ColimitLongExact.Ladder.{max u v w} (Over i)ᵒᵖ where
  D₄ n := extDiagram 𝒜'' F n
  M n := extDiagram 𝒜 F n
  D₁ n := extDiagram 𝒜' F n
  a n := precompNat F n S.π
  b n := precompNat F n S.φ
  δ n := S.deltaNat F n
  T₄ n := AddCommGrpCat.of (Ext.{max u v w} 𝒜''.top 𝒢 n)
  TM n := AddCommGrpCat.of (Ext.{max u v w} 𝒜.top 𝒢 n)
  T₁ n := AddCommGrpCat.of (Ext.{max u v w} 𝒜'.top 𝒢 n)
  A n := precompTop (𝒢 := 𝒢) n S.π
  B' n := precompTop (𝒢 := 𝒢) n S.φ
  Δ n := S.deltaTop 𝒢 n
  wab n := S.w_ab n
  wbδ n := S.w_bδ n
  wδa n := S.w_δa n
  exact_ab n := S.exact_ab n
  exact_bδ n := S.exact_bδ n
  exact_δa n := S.exact_δa n
  mono_a := by
    have : ∀ A : (Over i)ᵒᵖ, Mono ((precompNat F 0 S.π).app A) := fun A => by
      have : Epi (S.π.app A.unop) := (S.shortExact A.unop).epi_g
      exact (AddCommGrpCat.mono_iff_injective _).mpr
        (Ext.precomp_mk₀_injective_of_epi (F.obj A.unop.left) (S.π.app A.unop))
    exact NatTrans.mono_of_mono_app _
  wAB n := by
    ext x
    have key : ∀ y : Ext.{max u v w} 𝒜''.top 𝒢 n,
        (Ext.mk₀ S.φ.top).comp ((Ext.mk₀ S.π.top).comp y (zero_add n)) (zero_add n) = 0 :=
      fun y => by rw [Ext.mk₀_comp_mk₀_assoc, S.w_top, Ext.mk₀_zero, Ext.zero_comp]
    exact key x
  wBΔ n := by
    ext x
    have key : ∀ y : Ext.{max u v w} 𝒜.top 𝒢 n,
        S.shortExact_top.extClass.comp ((Ext.mk₀ S.φ.top).comp y (zero_add n))
          (add_comm 1 n) = 0 := fun y =>
      ShortComplex.ShortExact.extClass_comp_assoc S.shortExact_top y
    exact key x
  wΔA n := by
    ext x
    have key : ∀ y : Ext.{max u v w} 𝒜'.top 𝒢 n,
        (Ext.mk₀ S.π.top).comp (S.shortExact_top.extClass.comp y (add_comm 1 n))
          (zero_add (n + 1)) = 0 := fun y =>
      ShortComplex.ShortExact.comp_extClass_assoc S.shortExact_top y (add_comm 1 n)
    exact key x
  exact_AB n := Ext.contravariant_sequence_exact₂' S.shortExact_top 𝒢 n
  exact_BΔ n := Ext.contravariant_sequence_exact₁' S.shortExact_top 𝒢 n (n + 1) (add_comm 1 n)
  exact_ΔA n := Ext.contravariant_sequence_exact₃' S.shortExact_top 𝒢 n (n + 1) (add_comm 1 n)
  mono_A := by
    have : Epi S.π.top := S.shortExact_top.epi_g
    exact (AddCommGrpCat.mono_iff_injective _).mpr (Ext.precomp_mk₀_injective_of_epi 𝒢 S.π.top)
  c₄ n := colimit.desc _ (extCocone 𝒜'' F ι n @hι)
  cM n := colimit.desc _ (extCocone 𝒜 F ι n @hι)
  c₁ n := colimit.desc _ (extCocone 𝒜' F ι n @hι)
  comm_a n := by
    refine Stacks.Cohomology.ColimitLongExact.colimMap_desc_comm _ _ _ _ fun A => ?_
    ext x
    exact (extLeg_precomp F ι n S.π A.unop x).symm
  comm_b n := by
    refine Stacks.Cohomology.ColimitLongExact.colimMap_desc_comm _ _ _ _ fun A => ?_
    ext x
    exact (extLeg_precomp F ι n S.φ A.unop x).symm
  comm_δ n := by
    refine Stacks.Cohomology.ColimitLongExact.colimMap_desc_comm _ _ _ _ fun A => ?_
    ext x
    exact (extLeg_extClass_comp F ι n S A.unop x).symm

variable [HasExactColimitsOfShape (Over i)ᵒᵖ Ab.{max u v w}]

include S in
/-- **Two out of three, at the cokernel.** If the `Ext` cocones of `𝒜` and `𝒜'` are colimits in
every degree, so is that of `𝒜''`. -/
theorem nonempty_isColimit_right (hM : ∀ n, Nonempty (IsColimit (extCocone 𝒜 F ι n @hι)))
    (h₁ : ∀ n, Nonempty (IsColimit (extCocone 𝒜' F ι n @hι))) (n : ℕ) :
    Nonempty (IsColimit (extCocone 𝒜'' F ι n @hι)) :=
  (Stacks.Cohomology.ColimitLongExact.isIso_colimitDesc_iff _).mp
    ((S.ladder ι @hι).isIso_comparison₄
      (fun m => (Stacks.Cohomology.ColimitLongExact.isIso_colimitDesc_iff _).mpr (hM m))
      (fun m => (Stacks.Cohomology.ColimitLongExact.isIso_colimitDesc_iff _).mpr (h₁ m)) n)

include S in
/-- **Two out of three, at the middle term.** If the `Ext` cocones of `𝒜''` and `𝒜'` are colimits
in every degree, so is that of `𝒜`. -/
theorem nonempty_isColimit_middle (h₄ : ∀ n, Nonempty (IsColimit (extCocone 𝒜'' F ι n @hι)))
    (h₁ : ∀ n, Nonempty (IsColimit (extCocone 𝒜' F ι n @hι))) (n : ℕ) :
    Nonempty (IsColimit (extCocone 𝒜 F ι n @hι)) :=
  (Stacks.Cohomology.ColimitLongExact.isIso_colimitDesc_iff _).mp
    ((S.ladder ι @hι).isIso_comparisonM
      (fun m => (Stacks.Cohomology.ColimitLongExact.isIso_colimitDesc_iff _).mpr (h₄ m))
      (fun m => (Stacks.Cohomology.ColimitLongExact.isIso_colimitDesc_iff _).mpr (h₁ m)) n)

end FirstVariable.ShortExact

/-! ### Split first variables -/

namespace FirstVariable

/-- **A first variable split as a direct sum of two**, in the bicone sense, at every arrow and on
the colimit site, by morphisms of first variables. -/
structure Split (𝒜₁ 𝒜₂ 𝒜 : FirstVariable.{v, u, w} D uC hu K i) where
  /-- The inclusion of the first summand. -/
  inl : Hom 𝒜₁ 𝒜
  /-- The inclusion of the second summand. -/
  inr : Hom 𝒜₂ 𝒜
  /-- The projection to the first summand. -/
  fst : Hom 𝒜 𝒜₁
  /-- The projection to the second summand. -/
  snd : Hom 𝒜 𝒜₂
  inl_fst : ∀ A, inl.app A ≫ fst.app A = 𝟙 _
  inr_snd : ∀ A, inr.app A ≫ snd.app A = 𝟙 _
  inl_snd : ∀ A, inl.app A ≫ snd.app A = 0
  inr_fst : ∀ A, inr.app A ≫ fst.app A = 0
  total : ∀ A, fst.app A ≫ inl.app A + snd.app A ≫ inr.app A = 𝟙 _
  inl_fst_top : inl.top ≫ fst.top = 𝟙 _
  inr_snd_top : inr.top ≫ snd.top = 𝟙 _
  inl_snd_top : inl.top ≫ snd.top = 0
  inr_fst_top : inr.top ≫ fst.top = 0
  total_top : fst.top ≫ inl.top + snd.top ≫ inr.top = 𝟙 _

end FirstVariable

section Split

variable {𝒜₁ 𝒜₂ : FirstVariable.{v, u, w} D uC hu K i} (P : FirstVariable.Split 𝒜₁ 𝒜₂ 𝒜)
  [HasColimitsOfShape (Over i)ᵒᵖ Ab.{max u v w}]
  (hι : IsCompatible.{v, u, max u v w, max u v w} D uC hu F 𝒢.obj ι)

omit [∀ j, PreservesFiniteLimits (colimitPullback.{v, u, w} D uC K j)]
  [∀ j, EnoughInjectives (Sheaf (D.J j) Ab.{max u v w})]
  [∀ j, HasExt.{max u v w} (Sheaf (D.J j) Ab.{max u v w})]
  [HasExt.{max u v w} (Sheaf K.toGrothendieck Ab.{max u v w})]
  [∀ i, (uC i).IsContinuous (D.J i) K.toGrothendieck] in
/-- Two precompositions with morphisms of degree zero, as one. -/
theorem mk₀_comp_mk₀_comp {𝒞 : Type*} [Category* 𝒞] [Abelian 𝒞] [HasExt.{t} 𝒞]
    {X Y Z W : 𝒞} (a : X ⟶ Y) (b : Y ⟶ Z) (c : X ⟶ Z) (h : a ≫ b = c)
    (x : Ext.{t} Z W n) :
    (Ext.mk₀ a).comp ((Ext.mk₀ b).comp x (zero_add n)) (zero_add n) =
      (Ext.mk₀ c).comp x (zero_add n) := by
  rw [Ext.mk₀_comp_mk₀_assoc, h]

omit [∀ j, PreservesFiniteLimits (colimitPullback.{v, u, w} D uC K j)]
  [∀ j, EnoughInjectives (Sheaf (D.J j) Ab.{max u v w})]
  [∀ j, HasExt.{max u v w} (Sheaf (D.J j) Ab.{max u v w})]
  [HasExt.{max u v w} (Sheaf K.toGrothendieck Ab.{max u v w})]
  [∀ i, (uC i).IsContinuous (D.J i) K.toGrothendieck] in
/-- The sum of two pairs of precompositions with morphisms of degree zero, as one. -/
theorem mk₀_comp_mk₀_comp_add {𝒞 : Type*} [Category* 𝒞] [Abelian 𝒞] [HasExt.{t} 𝒞]
    {X Y₁ Y₂ W : 𝒞} (a₁ : X ⟶ Y₁) (b₁ : Y₁ ⟶ X) (a₂ : X ⟶ Y₂) (b₂ : Y₂ ⟶ X)
    (h : a₁ ≫ b₁ + a₂ ≫ b₂ = 𝟙 X) (x : Ext.{t} X W n) :
    (Ext.mk₀ a₁).comp ((Ext.mk₀ b₁).comp x (zero_add n)) (zero_add n) +
      (Ext.mk₀ a₂).comp ((Ext.mk₀ b₂).comp x (zero_add n)) (zero_add n) = x := by
  rw [Ext.mk₀_comp_mk₀_assoc, Ext.mk₀_comp_mk₀_assoc, ← Ext.add_comp, ← Ext.mk₀_add, h,
    Ext.mk₀_id_comp]

open FirstVariable.ShortExact

omit [HasColimitsOfShape (Over i)ᵒᵖ Ab]
  [∀ j, PreservesFiniteLimits (colimitPullback.{v, u, w} D uC K j)]
  [HasExt.{max u v w} (Sheaf K.toGrothendieck Ab.{max u v w})] in
/-- Precomposition along a retraction of first variables is a retraction of `Ext` diagrams. -/
theorem precompNat_comp_eq_id {X Y : FirstVariable.{v, u, w} D uC hu K i}
    (g : FirstVariable.Hom X Y) (g' : FirstVariable.Hom Y X) (h : ∀ A, g.app A ≫ g'.app A = 𝟙 _) :
    precompNat F n g' ≫ precompNat F n g = 𝟙 _ := by
  ext A x
  exact mk₀_comp_mk₀_comp_eq_self n _ _ (h A.unop) x

omit [HasColimitsOfShape (Over i)ᵒᵖ Ab]
  [∀ j, PreservesFiniteLimits (colimitPullback.{v, u, w} D uC K j)]
  [HasExt.{max u v w} (Sheaf K.toGrothendieck Ab.{max u v w})] in
/-- Precomposition along a composite zero morphism of first variables is zero. -/
theorem precompNat_comp_eq_zero {X Y Z : FirstVariable.{v, u, w} D uC hu K i}
    (g : FirstVariable.Hom X Y) (g' : FirstVariable.Hom Y Z) (h : ∀ A, g.app A ≫ g'.app A = 0) :
    precompNat F n g' ≫ precompNat F n g = 0 := by
  ext A x
  exact mk₀_comp_mk₀_comp_eq_zero n _ _ (h A.unop) x

omit [HasColimitsOfShape (Over i)ᵒᵖ Ab]
  [∀ j, PreservesFiniteLimits (colimitPullback.{v, u, w} D uC K j)]
  [HasExt.{max u v w} (Sheaf K.toGrothendieck Ab.{max u v w})] in
include P in
/-- The precompositions along the inclusions and projections of a split first variable sum to
the identity of its `Ext` diagram. -/
theorem FirstVariable.Split.precompNat_total :
    precompNat F n P.inl ≫ precompNat F n P.fst + precompNat F n P.inr ≫ precompNat F n P.snd =
      𝟙 _ := by
  ext A x
  exact mk₀_comp_mk₀_comp_add n _ _ _ _ (P.total A.unop) x

/-- The `Ext` groups out of a split first variable on the colimit site, as a biproduct. -/
def FirstVariable.Split.topIso :
    AddCommGrpCat.of (Ext.{max u v w} 𝒜.top 𝒢 n) ≅
      AddCommGrpCat.of (Ext.{max u v w} 𝒜₁.top 𝒢 n) ⊞ AddCommGrpCat.of (Ext.{max u v w} 𝒜₂.top 𝒢 n)
    where
  hom := biprod.lift (precompTop n P.inl) (precompTop n P.inr)
  inv := biprod.desc (precompTop n P.fst) (precompTop n P.snd)
  hom_inv_id := by
    rw [biprod.lift_desc]
    have key : ∀ y : Ext.{max u v w} 𝒜.top 𝒢 n,
        (Ext.mk₀ P.fst.top).comp ((Ext.mk₀ P.inl.top).comp y (zero_add n)) (zero_add n) +
          (Ext.mk₀ P.snd.top).comp ((Ext.mk₀ P.inr.top).comp y (zero_add n)) (zero_add n) = y :=
      fun y => mk₀_comp_mk₀_comp_add n _ _ _ _ P.total_top y
    ext x
    exact key x
  inv_hom_id := by
    have e₁ : precompTop (𝒢 := 𝒢) n P.fst ≫ precompTop n P.inl = 𝟙 _ := by
      have key : ∀ y : Ext.{max u v w} 𝒜₁.top 𝒢 n,
          (Ext.mk₀ P.inl.top).comp ((Ext.mk₀ P.fst.top).comp y (zero_add n)) (zero_add n) = y :=
        fun y => (mk₀_comp_mk₀_comp n _ _ _ P.inl_fst_top y).trans (Ext.mk₀_id_comp y)
      ext x
      exact key x
    have e₂ : precompTop (𝒢 := 𝒢) n P.snd ≫ precompTop n P.inr = 𝟙 _ := by
      have key : ∀ y : Ext.{max u v w} 𝒜₂.top 𝒢 n,
          (Ext.mk₀ P.inr.top).comp ((Ext.mk₀ P.snd.top).comp y (zero_add n)) (zero_add n) = y :=
        fun y => (mk₀_comp_mk₀_comp n _ _ _ P.inr_snd_top y).trans (Ext.mk₀_id_comp y)
      ext x
      exact key x
    have e₃ : precompTop (𝒢 := 𝒢) n P.fst ≫ precompTop n P.inr = 0 := by
      have key : ∀ y : Ext.{max u v w} 𝒜₁.top 𝒢 n,
          (Ext.mk₀ P.inr.top).comp ((Ext.mk₀ P.fst.top).comp y (zero_add n)) (zero_add n) = 0 :=
        fun y => (mk₀_comp_mk₀_comp n _ _ _ P.inr_fst_top y).trans
          (by rw [Ext.mk₀_zero, Ext.zero_comp])
      ext x
      exact key x
    have e₄ : precompTop (𝒢 := 𝒢) n P.snd ≫ precompTop n P.inl = 0 := by
      have key : ∀ y : Ext.{max u v w} 𝒜₂.top 𝒢 n,
          (Ext.mk₀ P.inl.top).comp ((Ext.mk₀ P.snd.top).comp y (zero_add n)) (zero_add n) = 0 :=
        fun y => (mk₀_comp_mk₀_comp n _ _ _ P.inl_snd_top y).trans
          (by rw [Ext.mk₀_zero, Ext.zero_comp])
      ext x
      exact key x
    refine biprod.hom_ext' _ _ (biprod.hom_ext _ _ ?_ ?_) (biprod.hom_ext _ _ ?_ ?_)
    · rw [biprod.inl_desc_assoc, Category.assoc, biprod.lift_fst, e₁]
      simp
    · rw [biprod.inl_desc_assoc, Category.assoc, biprod.lift_snd, e₃]
      simp
    · rw [biprod.inr_desc_assoc, Category.assoc, biprod.lift_fst, e₄]
      simp
    · rw [biprod.inr_desc_assoc, Category.assoc, biprod.lift_snd, e₂]
      simp

include P in
/-- **The `Ext` colimit property for a split first variable**, from those of its summands. -/
theorem FirstVariable.Split.nonempty_isColimit
    (h₁ : Nonempty (IsColimit (extCocone 𝒜₁ F ι n @hι)))
    (h₂ : Nonempty (IsColimit (extCocone 𝒜₂ F ι n @hι))) :
    Nonempty (IsColimit (extCocone 𝒜 F ι n @hι)) := by
  have hsplit := Stacks.Cohomology.ColimitLongExact.isIso_of_split (precompNat F n P.inl)
    (precompNat F n P.inr) (precompNat F n P.fst) (precompNat F n P.snd)
    (precompNat_comp_eq_id F n P.inl P.fst P.inl_fst)
    (precompNat_comp_eq_id F n P.inr P.snd P.inr_snd)
    (precompNat_comp_eq_zero F n P.inr P.fst P.inr_fst)
    (precompNat_comp_eq_zero F n P.inl P.snd P.inl_snd) (P.precompNat_total F n)
    (extCocone 𝒜₁ F ι n @hι) (extCocone 𝒜₂ F ι n @hι) h₁.some h₂.some
    (colimit.desc _ (extCocone 𝒜 F ι n @hι) ≫ (P.topIso (𝒢 := 𝒢) n).hom)
    (by
      refine (Category.assoc _ _ _).trans ((congrArg _ (biprod.lift_fst _ _)).trans ?_)
      exact (colimMap_desc_comm_apply _ _ _ _ fun A x =>
        (extLeg_precomp F ι n P.inl A.unop x).symm).symm)
    (by
      refine (Category.assoc _ _ _).trans ((congrArg _ (biprod.lift_snd _ _)).trans ?_)
      exact (colimMap_desc_comm_apply _ _ _ _ fun A x =>
        (extLeg_precomp F ι n P.inr A.unop x).symm).symm)
  have : IsIso (colimit.desc _ (extCocone 𝒜 F ι n @hι)) :=
    @IsIso.of_isIso_comp_right _ _ _ _ _ _ (P.topIso (𝒢 := 𝒢) n).hom (Iso.isIso_hom _) hsplit
  exact (Stacks.Cohomology.ColimitLongExact.isIso_colimitDesc_iff _).mp inferInstance

end Split

end Stacks.WeakSites.ExtColimit

end
