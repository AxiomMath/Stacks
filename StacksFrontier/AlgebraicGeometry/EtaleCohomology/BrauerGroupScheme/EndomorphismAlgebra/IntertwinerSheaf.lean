module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BrauerGroupScheme.EndomorphismAlgebra.ModuleConjugation

/-!
# The intertwiner sheaf and evaluation

Scalar-action instances on sections over a ringed space, the internal hom `SheafHom(F, G)` of two
sheaves of modules on a scheme, the subsheaf of `SheafHom(F, G)` of sections intertwining the
endomorphism sheaves along a morphism `α`, and the evaluation morphism `F ⊗ L ⟶ G`. Criteria for
invertibility of a sheaf with local one-element bases and for evaluation to be an isomorphism.
-/
@[expose] public section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
  Stacks.SheafOfModules.TensorStalkRingedSpace

universe u

namespace Stacks.EtaleCohomology

/-! ### Sheafification on a localized site of opens

The local-generator data of a finite locally free sheaf of modules is indexed by the slice sites
`J/U`, so stating it asks for `HasWeakSheafify` and `WEqualsLocallyBijective` on every slice site
of the opens of a scheme. Deriving those from the general machinery at each of the several
occurrences below is what pushes those statements over the typeclass budget; naming them once
makes each occurrence a single step. -/

/-- Abelian groups have a sheafification on the slice site of an open of a topological space. -/
instance hasWeakSheafifyOverOpens {T : Type u} [TopologicalSpace T] (U : Opens T) :
    HasWeakSheafify ((Opens.grothendieckTopology T).over U) AddCommGrpCat.{u} :=
  inferInstance

/-- `hasWeakSheafifyOverOpens` with the head of `HasWeakSheafify` written out, so that a goal
stated in the unfolded form is also matched in one step. -/
instance isRightAdjointSheafToPresheafOverOpens {T : Type u} [TopologicalSpace T] (U : Opens T) :
    (sheafToPresheaf ((Opens.grothendieckTopology T).over U) AddCommGrpCat.{u}).IsRightAdjoint :=
  inferInstance

/-- On the slice site of an open of a topological space, the weak equivalences of presheaves of
abelian groups are the locally bijective maps. -/
instance wEqualsLocallyBijectiveOverOpens {T : Type u} [TopologicalSpace T] (U : Opens T) :
    ((Opens.grothendieckTopology T).over U).WEqualsLocallyBijective AddCommGrpCat.{u} :=
  inferInstance

/-! ### Scalar actions on sections over a ringed space

The sections of an `O_X`-module over an open `U` carry a scalar action of the section ring, and
that ring has three spellings on a ringed space: the commutative `X.presheaf.obj U`, the
`RingCat`-valued `(O X).obj U` that `PresheafOfModules (O X)` uses, and
`(structureSheaf X.sheaf).obj.obj U`. They are the same ring, but `TopCat.Sheaf` is semireducible,
so instance search cannot pass between the spellings on its own. The instances below record the
identifications, in the manner of the ones in
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/SheafHomLeftExact.lean`. -/

/-- Sections over `U` of an `O_X`-module form a module over the commutative section ring
`O_X(U) = X.presheaf.obj U`. -/
private noncomputable instance modulePresheafSections {X : RingedSpace.{u}}
    {M : SheafOfModules.{u} (structureSheaf X.sheaf)} {U : (Opens X.carrier)ᵒᵖ} :
    Module (X.presheaf.obj U) (M.val.obj U) :=
  inferInstanceAs (Module ((structureSheaf X.sheaf).obj.obj U) (M.val.obj U))

/-- `modulePresheafSections` with the scalar ring written as the `RingCat`-valued structure
presheaf `O X`, which is the spelling `PresheafOfModules (O X)` uses. -/
private noncomputable instance moduleOSections {X : RingedSpace.{u}}
    {M : SheafOfModules.{u} (structureSheaf X.sheaf)} {U : (Opens X.carrier)ᵒᵖ} :
    Module ((O X).obj U) (M.val.obj U) :=
  inferInstanceAs (Module ((structureSheaf X.sheaf).obj.obj U) (M.val.obj U))

/-- The section ring is commutative, so its two actions on sections commute. Needed by the
tensor-product machinery in the `O X` spelling of the scalar ring. -/
private noncomputable instance smulCommClassOSections {X : RingedSpace.{u}}
    {M : SheafOfModules.{u} (structureSheaf X.sheaf)} {U : (Opens X.carrier)ᵒᵖ} :
    SMulCommClass ((O X).obj U) ((O X).obj U) (M.val.obj U) :=
  inferInstanceAs (SMulCommClass (X.presheaf.obj U) (X.presheaf.obj U) (M.val.obj U))

/-- Sections of the restriction `L|_U` over an object `V` of the slice site, with the restriction
written as the pushforward it unfolds to, form a module over the slice-site structure sheaf. -/
private noncomputable instance moduleSlicePushforward {X : TopCat.{u}}
    {R : TopCat.Sheaf CommRingCat.{u} X} {L : SheafOfModules.{u} (structureSheaf R)}
    {U : Opens X} {V : (Over U)ᵒᵖ} :
    Module (((structureSheaf R).over U).obj.obj V)
      (((PresheafOfModules.pushforward₀ (Over.forget U)
          ((sheafToPresheaf (Opens.grothendieckTopology X) RingCat.{u}).obj
            (structureSheaf R))).obj L.val).obj V) :=
  ((L.over U).val.obj V).isModule

/-- Restriction of scalars does not change the underlying module, so a section of the structure
sheaf on the smaller open acts on a restricted section. -/
private noncomputable instance modulePresheafRestrictScalars {X : RingedSpace.{u}}
    {U V : (Opens X.carrier)ᵒᵖ}
    {f : (structureSheaf X.sheaf).obj.obj U ⟶ (structureSheaf X.sheaf).obj.obj V}
    {N : ModuleCat.{u} ((structureSheaf X.sheaf).obj.obj V)} :
    Module (X.presheaf.obj V) ((ModuleCat.restrictScalars (RingCat.Hom.hom f)).obj N) :=
  inferInstanceAs (Module ((structureSheaf X.sheaf).obj.obj V) N)

/-- The internal hom of two sheaves of modules on a scheme, packaged with the identification of its
sections over an open `U` with the morphisms `F|_U ⟶ G|_U`. -/
private noncomputable def internalSheafHom
    (S : Scheme.{u})
    (F G : SheafOfModules.{u} (structureSheaf S.sheaf)) :
    SheafHom S.sheaf F G where
  obj := {
    val := internalHom S.sheaf.obj F.val G.val
    isSheaf := internalHom_isSheaf S.sheaf.obj F.val G.val G.isSheaf }
  sectionsEquiv U := by
    change ((restrFun S.sheaf.obj U).obj F.val ⟶
      (restrFun S.sheaf.obj U).obj G.val) ≃+ (F.over U ⟶ G.over U)
    let e : (F.over U ⟶ G.over U) ≃
        ((restrFun S.sheaf.obj U).obj F.val ⟶ (restrFun S.sheaf.obj U).obj G.val) :=
      (SheafOfModules.fullyFaithfulForget ((structureSheaf S.sheaf).over U)).homEquiv
        (X := F.over U) (Y := G.over U)
    exact
      { toFun := e.symm
        invFun := e
        left_inv := e.apply_symm_apply
        right_inv := e.symm_apply_apply
        map_add' := by
          intro f g
          apply e.injective
          simp only [Equiv.apply_symm_apply]
          rfl }
  restrict_natural := by
    intro U V hVU s W hWV x
    change ((homRestr S.sheaf.obj F.val G.val (homOfLE hVU) s).app
      (op (Over.mk (homOfLE hWV)))).hom x = _
    rfl
  smul_natural := by
    intro U r s W hWU x
    change ((smulHom S.sheaf.obj F.val G.val U r s).app
      (op (Over.mk (homOfLE hWU)))).hom x = _
    rfl



/-- The component at an open `V ≤ U` of a section of an internal hom over `U`, as a map on
sections of `F` over `V`. -/
private noncomputable abbrev sheafHomApp
    {X : TopCat.{u}} {R : TopCat.Sheaf CommRingCat.{u} X}
    {F G : SheafOfModules.{u} (structureSheaf R)} (H : SheafHom R F G)
    (U V : Opens X) (h : V ≤ U) (t : H.obj.val.obj (op U)) :
    F.val.obj (op V) →ₗ[R.obj.obj (op V)] G.val.obj (op V) :=
  ((H.sectionsEquiv U t).val.app (op (Over.mk (homOfLE h)))).hom

/-- The zero section of an internal hom acts as the zero map on every component. -/
private lemma sheafHomApp_zero
    {X : TopCat.{u}} {R : TopCat.Sheaf CommRingCat.{u} X}
    {F G : SheafOfModules.{u} (structureSheaf R)} (H : SheafHom R F G)
    (U V : Opens X) (h : V ≤ U) (x : F.val.obj (op V)) :
    sheafHomApp H U V h 0 x = 0 := by
  dsimp only [sheafHomApp]
  rw [map_zero]
  rfl

/-- Components of a sum of sections of an internal hom add. -/
private lemma sheafHomApp_add
    {X : TopCat.{u}} {R : TopCat.Sheaf CommRingCat.{u} X}
    {F G : SheafOfModules.{u} (structureSheaf R)} (H : SheafHom R F G)
    (U V : Opens X) (h : V ≤ U) (t t' : H.obj.val.obj (op U))
    (x : F.val.obj (op V)) :
    sheafHomApp H U V h (t + t') x =
      sheafHomApp H U V h t x + sheafHomApp H U V h t' x := by
  dsimp only [sheafHomApp]
  rw [map_add]
  rfl

/-- The component of a scaled section of an internal hom is the component scaled by the restricted
scalar. -/
private lemma sheafHomApp_smul
    {X : TopCat.{u}} {R : TopCat.Sheaf CommRingCat.{u} X}
    {F G : SheafOfModules.{u} (structureSheaf R)} (H : SheafHom R F G)
    (U V : Opens X) (h : V ≤ U) (r : (structureSheaf R).obj.obj (op U))
    (t : H.obj.val.obj (op U)) (x : F.val.obj (op V)) :
    sheafHomApp H U V h (r • t) x =
      (structureSheaf R).obj.map (homOfLE h).op r • sheafHomApp H U V h t x :=
  H.smul_natural U r t h x

/-- Restricting a section of an internal hom and then taking a component is taking the component
directly. -/
private lemma sheafHomApp_restrict
    {X : TopCat.{u}} {R : TopCat.Sheaf CommRingCat.{u} X}
    {F G : SheafOfModules.{u} (structureSheaf R)} (H : SheafHom R F G)
    {U V W : Opens X} (hVU : V ≤ U) (hWV : W ≤ V)
    (t : H.obj.val.obj (op U)) (x : F.val.obj (op W)) :
    sheafHomApp H V W hWV (H.obj.val.map (homOfLE hVU).op t) x =
      sheafHomApp H U W (hWV.trans hVU) t x :=
  (H.restrict_natural hVU t hWV x).symm

/-- The components of a section of an internal hom commute with restriction in `F` and `G`. -/
private lemma sheafHomApp_naturality
    {X : TopCat.{u}} {R : TopCat.Sheaf CommRingCat.{u} X}
    {F G : SheafOfModules.{u} (structureSheaf R)} (H : SheafHom R F G)
    {U V W : Opens X} (hVU : V ≤ U) (hWV : W ≤ V)
    (t : H.obj.val.obj (op U)) (x : F.val.obj (op V)) :
    G.val.map (homOfLE hWV).op (sheafHomApp H U V hVU t x) =
      sheafHomApp H U W (hWV.trans hVU) t (F.val.map (homOfLE hWV).op x) := by
  let k : Over.mk (homOfLE (hWV.trans hVU)) ⟶ Over.mk (homOfLE hVU) :=
    Over.homMk (homOfLE hWV)
  exact (congrArg (fun f => f.hom x) ((H.sectionsEquiv U t).val.naturality k.op)).symm

/-- The subpresheaf of the internal hom `SheafHom(F, G)` whose sections over `U` intertwine the
endomorphism sheaves of `F` and `G` along a given morphism `α`, on every open subset of `U`. -/
private def sheafIntertwinerSubmodule
    {X : TopCat.{u}} {R : TopCat.Sheaf CommRingCat.{u} X}
    {F G : SheafOfModules.{u} (structureSheaf R)}
    (HFF : SheafHom R F F) (HGG : SheafHom R G G) (HFG : SheafHom R F G)
    (α : HFF.obj ⟶ HGG.obj) : HFG.obj.val.Submodule where
  obj U :=
    { carrier := {t | ∀ (V : Opens X) (hVU : V ≤ U.unop)
        (s : HFF.obj.val.obj (op V)) (f : F.val.obj (op V)),
        sheafHomApp HGG V V le_rfl (α.val.app (op V) s)
            (sheafHomApp HFG U.unop V hVU t f) =
          sheafHomApp HFG U.unop V hVU t (sheafHomApp HFF V V le_rfl s f)}
      zero_mem' := by
        intro V hVU s f
        rw [sheafHomApp_zero, sheafHomApp_zero, map_zero]
      add_mem' := by
        intro t t' ht ht' V hVU s f
        rw [sheafHomApp_add, sheafHomApp_add, map_add,
          ht V hVU s f, ht' V hVU s f]
      smul_mem' := by
        intro r t ht V hVU s f
        change sheafHomApp HGG V V le_rfl (α.val.app (op V) s)
            (sheafHomApp HFG U.unop V hVU (r • t) f) = _
        rw [sheafHomApp_smul, sheafHomApp_smul, map_smul]
        rw [ht V hVU s f] }
  map {U V} k := by
    intro t ht W hWV s f
    change sheafHomApp HGG W W le_rfl (α.val.app (op W) s)
        (sheafHomApp HFG V.unop W hWV (HFG.obj.val.map k t) f) =
      sheafHomApp HFG V.unop W hWV (HFG.obj.val.map k t)
        (sheafHomApp HFF W W le_rfl s f)
    have hk : k = (homOfLE (leOfHom k.unop)).op := Subsingleton.elim _ _
    rw [hk]
    rw [sheafHomApp_restrict HFG (leOfHom k.unop) hWV,
      sheafHomApp_restrict HFG (leOfHom k.unop) hWV]
    exact ht W (hWV.trans (leOfHom k.unop)) s f

/-- The intertwiner subsheaf of `SheafHom(F, G)`. The intertwining condition is local, so the
subpresheaf of `sheafIntertwinerSubmodule` is a subsheaf. -/
private noncomputable def sheafIntertwiner
    {X : TopCat.{u}} {R : TopCat.Sheaf CommRingCat.{u} X}
    {F G : SheafOfModules.{u} (structureSheaf R)}
    (HFF : SheafHom R F F) (HGG : SheafHom R G G) (HFG : SheafHom R F G)
    (α : HFF.obj ⟶ HGG.obj) : HFG.obj.Submodule where
  toSubmodule := sheafIntertwinerSubmodule HFF HGG HFG α
  isSheaf {U} t ht := by
    intro V hVU s f
    apply G.isSheaf.isSeparated _ _
      ((Opens.grothendieckTopology X).pullback_stable (homOfLE hVU) ht)
    intro W k hk
    have hWV : W ≤ V := leOfHom k
    change G.val.map (homOfLE hWV).op
        (sheafHomApp HGG V V le_rfl (α.val.app (op V) s)
          (sheafHomApp HFG U.unop V hVU t f)) =
      G.val.map (homOfLE hWV).op
        (sheafHomApp HFG U.unop V hVU t (sheafHomApp HFF V V le_rfl s f))
    rw [sheafHomApp_naturality, sheafHomApp_naturality,
      sheafHomApp_naturality, sheafHomApp_naturality]
    change ∀ (Z : Opens X) (hZW : Z ≤ W)
      (s : HFF.obj.val.obj (op Z)) (f : F.val.obj (op Z)),
      sheafHomApp HGG Z Z le_rfl (α.val.app (op Z) s)
          (sheafHomApp HFG W Z hZW
            (HFG.obj.val.map (homOfLE (hWV.trans hVU)).op t) f) =
        sheafHomApp HFG W Z hZW
          (HFG.obj.val.map (homOfLE (hWV.trans hVU)).op t)
          (sheafHomApp HFF Z Z le_rfl s f) at hk
    have hk' := hk W le_rfl
      (HFF.obj.val.map (homOfLE hWV).op s) (F.val.map (homOfLE hWV).op f)
    simp only [sheafHomApp_restrict HFG (hWV.trans hVU) le_rfl,
      PresheafOfModules.naturality_apply,
      sheafHomApp_restrict HGG hWV le_rfl] at hk'
    have hA := sheafHomApp_restrict HFG (hWV.trans hVU) le_rfl t
      (F.val.map (homOfLE hWV).op f)
    have hB := sheafHomApp_restrict HFF hWV le_rfl s
      (F.val.map (homOfLE hWV).op f)
    exact ((congrArg
      (fun y => sheafHomApp HGG V W hWV (α.val.app (op V) s) y) hA).symm.trans hk').trans
        (congrArg (fun y => sheafHomApp HFG U.unop W (hWV.trans hVU) t y) hB)

/-- A section of an internal hom over `U`, read as a linear map on the sections over `U` itself,
linearly in the section. -/
private noncomputable def sheafHomSectionLinearMap
    {X : TopCat.{u}} {R : TopCat.Sheaf CommRingCat.{u} X}
    {F G : SheafOfModules.{u} (structureSheaf R)} (H : SheafHom R F G)
    (U : Opens X) :
    H.obj.val.obj (op U) →ₗ[R.obj.obj (op U)]
      (F.val.obj (op U) →ₗ[R.obj.obj (op U)] G.val.obj (op U)) where
  toFun := sheafHomApp H U U le_rfl
  map_add' s t := by ext f; exact sheafHomApp_add H U U le_rfl s t f
  map_smul' r t := by
    ext f
    have h := sheafHomApp_smul H U U le_rfl r t f
    have hr : (structureSheaf R).obj.map (homOfLE (le_refl U)).op r = r := by
      change (R.obj.map (𝟙 (op U))).hom r = r
      rw [CategoryTheory.Functor.map_id]
      rfl
    rw [hr] at h
    exact h

/-- Evaluation of a section of `L` on a section of `F`, bilinearly, over the commutative section
ring. Naming it fixes one spelling of the scalar ring: the two factors act over different
spellings of the ring of sections over `U`, so composing them without this ascription asks
instance search to identify the spellings, which it cannot do. -/
private noncomputable def sheafHomEvaluationBilin
    (X : RingedSpace.{u}) {F G L : SheafOfModules.{u} (structureSheaf X.sheaf)}
    (H : SheafHom X.sheaf F G) (ι : L ⟶ H.obj) (U : (Opens X.carrier)ᵒᵖ) :
    L.val.obj U →ₗ[X.presheaf.obj U] (F.val.obj U →ₗ[X.presheaf.obj U] G.val.obj U) :=
  LinearMap.comp
    (show H.obj.val.obj U →ₗ[X.presheaf.obj U]
        (F.val.obj U →ₗ[X.presheaf.obj U] G.val.obj U) from
      sheafHomSectionLinearMap H U.unop)
    (show L.val.obj U →ₗ[X.presheaf.obj U] H.obj.val.obj U from (ι.val.app U).hom)

/-- Evaluation `F ⊗ L ⟶ G` at the level of presheaves, for a sheaf `L` mapping to an internal hom
`SheafHom(F, G)`: a local tensor `f ⊗ l` goes to the value at `f` of the map `l` names. -/
private noncomputable def sheafHomEvaluationPresheaf
    (X : RingedSpace.{u}) {F G L : SheafOfModules.{u} (structureSheaf X.sheaf)}
    (H : SheafHom X.sheaf F G) (ι : L ⟶ H.obj) :
    (PresheafOfModules.tensorObj (O := (X).presheaf) (F.val) (L.val)) ⟶ G.val where
  app U := ModuleCat.ofHom (TensorProduct.lift
    (sheafHomEvaluationBilin X H ι U).flip)
  naturality {U V} k := by
    apply ModuleCat.hom_ext
    apply TensorProduct.ext'
    intro f l
    change sheafHomApp H V.unop V.unop le_rfl
        (ι.val.app V (L.val.map k l)) (F.val.map k f) =
      G.val.map k (sheafHomApp H U.unop U.unop le_rfl (ι.val.app U l) f)
    rw [PresheafOfModules.naturality_apply]
    have hVU : V.unop ≤ U.unop := leOfHom k.unop
    change sheafHomApp H V.unop V.unop le_rfl
        (H.obj.val.map (homOfLE hVU).op (ι.val.app U l))
        (F.val.map (homOfLE hVU).op f) =
      G.val.map (homOfLE hVU).op
        (sheafHomApp H U.unop U.unop le_rfl (ι.val.app U l) f)
    exact (sheafHomApp_restrict H hVU le_rfl (ι.val.app U l)
        (F.val.map (homOfLE hVU).op f)).trans
      (sheafHomApp_naturality H le_rfl hVU (ι.val.app U l) f).symm

/-- Evaluation `F ⊗ L ⟶ G` as a morphism of sheaves of modules, obtained from the presheaf-level
evaluation by the sheafification adjunction. -/
private noncomputable def sheafHomEvaluation
    (X : RingedSpace.{u}) {F G L : SheafOfModules.{u} (structureSheaf X.sheaf)}
    (H : SheafHom X.sheaf F G) (ι : L ⟶ H.obj) :
    (((Stacks.SheafOfModules.Tensor.sheafTensor ⟨((X)).presheaf, ((X)).IsSheaf⟩).obj (F)).obj
      (L)) ⟶ G :=
  ((PresheafOfModules.sheafificationAdjunction
    (𝟙 (structureSheafRing X).obj)).homEquiv _ _).symm
      (sheafHomEvaluationPresheaf X H ι)

/-- Evaluation sends the image of a local tensor `f ⊗ l` to the value at `f` of the map that `l`
names. -/
private lemma sheafHomEvaluation_tmul
    (X : RingedSpace.{u}) {F G L : SheafOfModules.{u} (structureSheaf X.sheaf)}
    (H : SheafHom X.sheaf F G) (ι : L ⟶ H.obj)
    (U : Opens X) (f : F.val.obj (op U)) (l : L.val.obj (op U)) :
    (sheafHomEvaluation X H ι).val.app (op U)
        (toTensorSheafSection X F L (op U) (f ⊗ₜ[X.presheaf.obj (op U)] l)) =
      sheafHomApp H U U le_rfl (ι.val.app (op U) l) f := by
  have h : ((PresheafOfModules.sheafificationAdjunction
        (𝟙 (structureSheafRing X).obj)).homEquiv
          ((PresheafOfModules.tensorObj (O := (X).presheaf) (F.val) (L.val))) G)
      (sheafHomEvaluation X H ι) = sheafHomEvaluationPresheaf X H ι :=
    ((PresheafOfModules.sheafificationAdjunction
      (𝟙 (structureSheafRing X).obj)).homEquiv _ G).apply_symm_apply
        (sheafHomEvaluationPresheaf X H ι)
  rw [Adjunction.homEquiv_unit
    (PresheafOfModules.sheafificationAdjunction (𝟙 (structureSheafRing X).obj))
    ((PresheafOfModules.tensorObj (O := (X).presheaf) (F.val) (L.val))) G
    (sheafHomEvaluation X H ι)] at h
  exact congrArg (fun q => (q.app (op U)).hom
    (f ⊗ₜ[X.presheaf.obj (op U)] l)) h

/-- Evaluation of the intertwiner sheaf transports the action of an endomorphism of `F` to the
action of its image under `α` on `G`. -/
private lemma sheafIntertwiner_evaluation_commutes
    (X : RingedSpace.{u}) {F G : SheafOfModules.{u} (structureSheaf X.sheaf)}
    (HFF : SheafHom X.sheaf F F) (HGG : SheafHom X.sheaf G G)
    (HFG : SheafHom X.sheaf F G) (α : HFF.obj ⟶ HGG.obj)
    (U : Opens X) (s : HFF.obj.val.obj (op U)) (f : F.val.obj (op U))
    (l : (sheafIntertwiner HFF HGG HFG α).toSheafOfModules.val.obj (op U)) :
    let L := (sheafIntertwiner HFF HGG HFG α).toSheafOfModules
    let ev := sheafHomEvaluation X HFG (sheafIntertwiner HFF HGG HFG α).ι
    sheafHomApp HGG U U le_rfl (α.val.app (op U) s)
        (ev.val.app (op U) (toTensorSheafSection X F L (op U)
          (f ⊗ₜ[X.presheaf.obj (op U)] l))) =
      ev.val.app (op U) (toTensorSheafSection X F L (op U)
        ((sheafHomApp HFF U U le_rfl s f) ⊗ₜ[X.presheaf.obj (op U)] l)) := by
  dsimp only
  rw [sheafHomEvaluation_tmul, sheafHomEvaluation_tmul]
  exact l.2 U le_rfl s f

/-- A morphism of presheaves of modules into a sheaf whose components are bijective on arbitrarily
small opens around every point induces an isomorphism after sheafification. -/
private lemma sheafify_isIso_of_locally_bijective
    (X : RingedSpace.{u}) {P : PresheafOfModules.{u} (O X)}
    {G : SheafOfModules.{u} (structureSheafRing X)} (f : P ⟶ G.val)
    (hf : ∀ (U : Opens X) (x : X), x ∈ U →
      ∃ (V : Opens X) (_ : V ⟶ U), x ∈ V ∧ Function.Bijective (f.app (op V))) :
    IsIso (((PresheafOfModules.sheafificationAdjunction
      (𝟙 (structureSheafRing X).obj)).homEquiv P G).symm f) := by
  let φ := (PresheafOfModules.toPresheaf (O X)).map f
  have hinj : Presheaf.IsLocallyInjective (JX X) φ := by
    constructor
    intro U t s h
    rw [Opens.mem_grothendieckTopology]
    intro x hx
    obtain ⟨V, k, hxV, hbij⟩ := hf U.unop x hx
    refine ⟨V, k, ?_, hxV⟩
    apply hbij.injective
    change φ.app (op V) (P.presheaf.map k.op t) =
      φ.app (op V) (P.presheaf.map k.op s)
    exact (NatTrans.naturality_apply φ k.op t).trans
      ((congrArg (G.val.presheaf.map k.op) h).trans
        (NatTrans.naturality_apply φ k.op s).symm)
  have hsurj : Presheaf.IsLocallySurjective (JX X) φ := by
    constructor
    intro U a
    rw [Opens.mem_grothendieckTopology]
    intro x hx
    obtain ⟨V, k, hxV, hbij⟩ := hf U x hx
    exact ⟨V, k, hbij.surjective _, hxV⟩
  have : IsIso ((PresheafOfModules.sheafification
      (R := structureSheafRing X) (𝟙 (structureSheafRing X).obj)).map f) := by
    rw [← isIso_iff_of_reflects_iso _ (SheafOfModules.toSheaf (structureSheafRing X))]
    exact ((JX X).W_iff _).mp ((JX X).W_of_isLocallyBijective φ)
  have hcounit : ((PresheafOfModules.sheafificationAdjunction
        (𝟙 (structureSheafRing X).obj)).homEquiv P G).symm f =
      (PresheafOfModules.sheafification (R := structureSheafRing X)
        (𝟙 (structureSheafRing X).obj)).map f ≫
        (PresheafOfModules.sheafificationAdjunction
          (𝟙 (structureSheafRing X).obj)).counit.app G :=
    Adjunction.homEquiv_counit
      (PresheafOfModules.sheafificationAdjunction (𝟙 (structureSheafRing X).obj)) P G f
  have hc : IsIso ((PresheafOfModules.sheafificationAdjunction
      (𝟙 (structureSheafRing X).obj)).counit.app G) :=
    NatIso.isIso_app_of_isIso _ G
  rw [hcounit]
  exact IsIso.comp_isIso' this hc

/-- The restriction of a section of `L` over `U` to an object `V` of the slice site, in the
spelling `L|_U` carries. Naming it fixes the `ModuleCat` index: the restricted section and a
section of `L|_U` over `V` have the same carrier but are indexed by two spellings of the section
ring, which instance search does not connect. -/
private noncomputable def overResSection
    {X : TopCat.{u}} {R : TopCat.Sheaf CommRingCat.{u} X}
    (L : SheafOfModules.{u} (structureSheaf R)) (U : Opens X)
    (t : L.val.obj (op U)) (V : (Over U)ᵒᵖ) : (L.over U).val.obj V :=
  L.val.map V.unop.hom.op t

/-- The restrictions of `overResSection` are the restrictions of the section. -/
private lemma overResSection_map
    {X : TopCat.{u}} {R : TopCat.Sheaf CommRingCat.{u} X}
    (L : SheafOfModules.{u} (structureSheaf R)) (U : Opens X)
    (t : L.val.obj (op U)) {V W : (Over U)ᵒᵖ} (k : V ⟶ W) :
    (L.over U).val.map k (overResSection L U t V) = overResSection L U t W := by
  change L.val.map k.unop.left.op (L.val.map V.unop.hom.op t) =
    L.val.map W.unop.hom.op t
  rw [← PresheafOfModules.map_comp_apply, ← op_comp, Over.w]

/-- The morphism from the structure sheaf of `U` to `F|_U` determined by a section of `F` over `U`,
sending a local scalar to that scalar times the restricted section. -/
private noncomputable def unitToSheafOverOfSection
    {X : TopCat.{u}} {R : TopCat.Sheaf CommRingCat.{u} X}
    (L : SheafOfModules.{u} (structureSheaf R)) (U : Opens X)
    (t : L.val.obj (op U)) : SheafOfModules.unit ((structureSheaf R).over U) ⟶ L.over U where
  val := {
    app V := ModuleCat.ofHom (LinearMap.toSpanSingleton
      (((structureSheaf R).over U).obj.obj V) ((L.over U).val.obj V)
      (overResSection L U t V))
    naturality {V W} k := by
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro r
      exact (congrArg (fun y => (((structureSheaf R).over U).obj.map k
            (show ((structureSheaf R).over U).obj.obj V from r)) • y)
          (overResSection_map L U t k)).symm.trans
        (PresheafOfModules.map_smul (L.over U).val k
          (show ((structureSheaf R).over U).obj.obj V from r)
          (overResSection L U t V)).symm }

/-- A section of `F` over `U` whose associated scalar-multiplication maps are bijective on every
open subset of `U` trivializes `F|_U`. -/
private lemma isIso_unitToSheafOverOfSection
    {X : TopCat.{u}} {R : TopCat.Sheaf CommRingCat.{u} X}
    (L : SheafOfModules.{u} (structureSheaf R)) (U : Opens X)
    (t : L.val.obj (op U))
    (ht : ∀ (V : Opens X) (hVU : V ≤ U),
      Function.Bijective (fun r : R.obj.obj (op V) => r • L.val.map (homOfLE hVU).op t)) :
    IsIso (unitToSheafOverOfSection L U t) := by
  have hcomp (V : (Over U)ᵒᵖ) :
      IsIso ((unitToSheafOverOfSection L U t).val.app V) := by
    rw [ConcreteCategory.isIso_iff_bijective]
    have hV : (homOfLE (leOfHom V.unop.hom) : V.unop.left ⟶ U) = V.unop.hom :=
      Subsingleton.elim _ _
    have h := ht V.unop.left (leOfHom V.unop.hom)
    rwa [hV] at h
  let e := PresheafOfModules.isoMk
    (fun V => asIso ((unitToSheafOverOfSection L U t).val.app V))
    (fun {_ _} k => (unitToSheafOverOfSection L U t).val.naturality k)
  have : IsIso ((SheafOfModules.forget ((structureSheaf R).over U)).map
      (unitToSheafOverOfSection L U t)) := by
    change IsIso e.hom
    infer_instance
  exact isIso_of_reflects_iso _ (SheafOfModules.forget _)

/-- A sheaf of modules with a local basis of one element around every point is invertible: the
scalar-multiplication map of the basis section trivializes the sheaf on that neighbourhood, and a
sheaf of modules trivial on a covering family is invertible. -/
private lemma isInvertible_of_locally_basis
    (X : RingedSpace.{u}) (L : SheafOfModules.{u} (structureSheaf X.sheaf))
    (hL : ∀ x : X, ∃ (U : Opens X) (t : L.val.obj (op U)), x ∈ U ∧
      ∀ (V : Opens X) (hVU : V ≤ U), Function.Bijective
        (fun r : X.presheaf.obj (op V) => r • L.val.map (homOfLE hVU).op t)) :
    Stacks.SheafOfModules.IsInvertible X.sheaf.obj (structureSheaf X.sheaf).property L := by
  choose U t hxU hbij using hL
  have hcov : (Opens.grothendieckTopology X.carrier).CoversTop U := by
    rw [Opens.coversTop_iff]
    exact top_unique fun x _ => Opens.mem_iSup.mpr ⟨x, hxU x⟩
  refine Stacks.SheafOfModules.isInvertible_of_coversTop_iso_unit _ _ L hcov fun x => ?_
  have := isIso_unitToSheafOverOfSection L (U x) (t x) (hbij x)
  exact (asIso (unitToSheafOverOfSection L (U x) (t x))).symm

/-- If a module `M` is free of rank one on a generator `t` and a bilinear map is bijective at `t`,
then the induced map on the tensor product is bijective. -/
private lemma tensor_lift_flip_bijective_of_basis
    {R P Q M : Type u} [CommRing R]
    [AddCommGroup P] [Module R P] [AddCommGroup Q] [Module R Q]
    [AddCommGroup M] [Module R M] (f : M →ₗ[R] (P →ₗ[R] Q)) (t : M)
    (ht : Function.Bijective (fun r : R => r • t))
    (hf : Function.Bijective (f t)) :
    Function.Bijective (TensorProduct.lift f.flip) := by
  let s := LinearEquiv.ofBijective (LinearMap.toSpanSingleton R M t) ht
  let T := LinearEquiv.ofBijective (f t) hf
  let e := s.symm.lTensor P ≪≫ₗ TensorProduct.rid R P ≪≫ₗ T
  have he : TensorProduct.lift f.flip = e.toLinearMap := by
    apply TensorProduct.ext'
    intro p l
    have hl : l = s.symm l • t := (s.apply_symm_apply l).symm
    change f l p = T (s.symm l • p)
    conv_lhs => rw [hl]
    simp only [map_smul, LinearMap.smul_apply]
    rfl
  rw [he]
  exact e.bijective

/-- Evaluation `F ⊗ L ⟶ G` is an isomorphism when, around every point, `L` has a basis of one
element whose associated map `F|_V ⟶ G|_V` is bijective. -/
private lemma sheafHomEvaluation_isIso_of_locally_basis
    (X : RingedSpace.{u}) {F G L : SheafOfModules.{u} (structureSheaf X.sheaf)}
    (H : SheafHom X.sheaf F G) (ι : L ⟶ H.obj)
    (hL : ∀ x : X, ∃ (U : Opens X) (t : L.val.obj (op U)), x ∈ U ∧
      (∀ (V : Opens X) (hVU : V ≤ U), Function.Bijective
        (fun r : X.presheaf.obj (op V) => r • L.val.map (homOfLE hVU).op t)) ∧
      (∀ (V : Opens X) (hVU : V ≤ U), Function.Bijective
        (sheafHomApp H U V hVU (ι.val.app (op U) t)))) :
    IsIso (sheafHomEvaluation X H ι) := by
  apply sheafify_isIso_of_locally_bijective
  intro W x hxW
  obtain ⟨U, t, hxU, hb, he⟩ := hL x
  let V := U ⊓ W
  let k : V ⟶ U := homOfLE inf_le_left
  refine ⟨V, homOfLE inf_le_right, ⟨hxU, hxW⟩, ?_⟩
  apply tensor_lift_flip_bijective_of_basis
    (sheafHomEvaluationBilin X H ι (op V))
    (L.val.map k.op t) (hb V inf_le_left)
  change Function.Bijective
    (sheafHomApp H V V le_rfl (ι.val.app (op V) (L.val.map k.op t)))
  rw [PresheafOfModules.naturality_apply]
  have heq : sheafHomApp H V V le_rfl (H.obj.val.map k.op (ι.val.app (op U) t)) =
      sheafHomApp H U V inf_le_left (ι.val.app (op U) t) := by
    ext f
    exact sheafHomApp_restrict H inf_le_left le_rfl _ _
  rw [heq]
  exact he V inf_le_left

end Stacks.EtaleCohomology
