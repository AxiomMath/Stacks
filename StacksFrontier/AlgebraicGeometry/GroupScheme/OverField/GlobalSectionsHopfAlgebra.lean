module

public import Mathlib.AlgebraicGeometry.Group.Affine
public import StacksFrontier.AlgebraicGeometry.Morphisms.GlobalSectionsTensorQcqs
public import StacksFrontier.AlgebraicGeometry.GroupScheme.OverField.Separated
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The Hopf algebra of global functions of a quasi-compact group scheme over a field

Let `k` be a field and `G` a group scheme over `k` whose underlying space is quasi-compact.
Then `Γ(G, 𝒪_G)` is a commutative Hopf algebra over `k`: its comultiplication is the pullback
of functions along the multiplication `G ×_k G → G`, read through the Künneth isomorphism
`Γ(G) ⊗[k] Γ(G) ≅ Γ(G ×_k G)`, its counit is evaluation at the unit section and its antipode is
the pullback along the inversion.  For affine `G` this is Mathlib's Hopf algebra of `G`; the point
here is that no affineness is needed.

## Main definitions

* `AlgebraicGeometry.qcqsOverField k`: the schemes quasi-compact and quasi-separated over
  `Spec k`, a property of objects of `Over (Spec k)` closed under finite products.
* `AlgebraicGeometry.qcqsGlobalSections k`: the global sections functor `algΓ` on that full
  subcategory; it preserves finite products (`isLimitAlgΓBinaryFan`, Künneth, and
  `isTerminalQcqsGlobalSectionsTensorUnit`).
* `AlgebraicGeometry.globalSectionsHopfAlgebra f`: the Hopf algebra structure on `Γ(G, ⊤)`.

## Main results

* `AlgebraicGeometry.globalSectionsTensorAlgEquiv_comul`,
  `AlgebraicGeometry.counit_globalSectionsHopfAlgebra`,
  `AlgebraicGeometry.antipode_globalSectionsHopfAlgebra`,
  `AlgebraicGeometry.algebraMap_globalSectionsHopfAlgebra`: the structure maps are those of `G`.

## Implementation notes

A finite-product-preserving functor between cartesian monoidal categories is monoidal
(`Functor.Monoidal.ofChosenFiniteProducts`) and so carries group objects to group objects
(`Functor.grpObjObj`); a group object of `(CommAlgCat k)ᵒᵖ` is a commutative Hopf algebra
(Mathlib, `Mathlib.Algebra.Category.CommHopfAlgCat`).  The global sections functor does not
preserve products on all of `Over (Spec k)`, so it is restricted to the full subcategory of
quasi-compact quasi-separated schemes, where Künneth
(`AlgebraicGeometry.bijective_globalSectionsTensorDesc`) says it does.  A group scheme over a
field is separated ([Stacks, Tag 047L]), so quasi-compactness of `G` is the only hypothesis.
-/

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory TensorProduct MonObj GrpObj

universe u

namespace AlgebraicGeometry

variable (k : Type u) [Field k]

/-- The schemes over `Spec k` which are quasi-compact and quasi-separated over `Spec k`. -/
def qcqsOverField : ObjectProperty (Over (Spec (CommRingCat.of k))) :=
  fun X => QuasiCompact X.hom ∧ QuasiSeparated X.hom

variable {k}

/-- Being quasi-compact and quasi-separated over `Spec k` is invariant under isomorphism. -/
lemma qcqsOverField_of_iso {X Y : Over (Spec (CommRingCat.of k))} (e : X ≅ Y)
    (hY : qcqsOverField k Y) : qcqsOverField k X := by
  obtain ⟨h1, h2⟩ := hY
  have : IsIso e.hom.left := inferInstanceAs (IsIso ((Over.forget _).mapIso e).hom)
  rw [qcqsOverField, ← Over.w e.hom]
  exact ⟨inferInstance, inferInstance⟩

/-- Being quasi-compact and quasi-separated over `Spec k` is closed under isomorphisms. -/
instance : (qcqsOverField k).IsClosedUnderIsomorphisms where
  of_iso e h := qcqsOverField_of_iso e.symm h

/-- A product over `Spec k` of quasi-compact quasi-separated schemes is one. -/
lemma qcqsOverField_tensor (X Y : Over (Spec (CommRingCat.of k))) (hX : qcqsOverField k X)
    (hY : qcqsOverField k Y) : qcqsOverField k (X ⊗ Y) := by
  obtain ⟨_, _⟩ := hX
  obtain ⟨_, _⟩ := hY
  show QuasiCompact (pullback.fst X.hom Y.hom ≫ X.hom) ∧
    QuasiSeparated (pullback.fst X.hom Y.hom ≫ X.hom)
  exact ⟨inferInstance, inferInstance⟩

/-- A terminal object of `Over (Spec k)` is quasi-compact and quasi-separated over `Spec k`. -/
instance : (qcqsOverField k).IsClosedUnderLimitsOfShape (Discrete.{0} PEmpty) where
  limitsOfShape_le := by
    rintro X ⟨p⟩
    have hX : IsTerminal X := isLimitEquivIsTerminalOfIsEmpty _ (Cone.mk _ p.π) p.isLimit
    refine qcqsOverField_of_iso (hX.uniqueUpToIso isTerminalTensorUnit) ?_
    change QuasiCompact (𝟙 _) ∧ QuasiSeparated (𝟙 _)
    exact ⟨inferInstance, inferInstance⟩

/-- A binary product of schemes quasi-compact and quasi-separated over `Spec k` is again
quasi-compact and quasi-separated over `Spec k`. -/
instance : (qcqsOverField k).IsClosedUnderLimitsOfShape (Discrete WalkingPair) where
  limitsOfShape_le := by
    rintro X ⟨p⟩
    have hc := (IsLimit.postcomposeHomEquiv (diagramIsoPair p.diag) _).symm p.isLimit
    exact qcqsOverField_of_iso
      (IsLimit.conePointUniqueUpToIso hc (tensorProductIsBinaryProduct _ _))
      (qcqsOverField_tensor _ _ (p.prop_diag_obj _) (p.prop_diag_obj _))

section Kunneth

variable (X Y : Over (Spec (CommRingCat.of k)))
  [QuasiCompact X.hom] [QuasiSeparated X.hom] [QuasiCompact Y.hom] [QuasiSeparated Y.hom]

/-- The global sections of a scheme over `Spec k`, as a `k`-algebra: the value of `algΓ`. -/
noncomputable abbrev globalSectionsAlg (Z : Over (Spec (CommRingCat.of k))) : CommAlgCat k :=
  ((algΓ (CommRingCat.of k)).obj Z).unop

/-- The Künneth isomorphism `Γ(X) ⊗[k] Γ(Y) ≃ Γ(X ×_k Y)` as an isomorphism of `k`-algebras,
for `X` and `Y` quasi-compact and quasi-separated over `Spec k`. -/
noncomputable def globalSectionsTensorAlgEquiv :
    (globalSectionsAlg X) ⊗[k] (globalSectionsAlg Y) ≃ₐ[k] (globalSectionsAlg (X ⊗ Y)) :=
  AlgEquiv.ofBijective
    (Algebra.TensorProduct.productMap ((algΓ (CommRingCat.of k)).map (fst X Y)).unop.hom
      ((algΓ (CommRingCat.of k)).map (snd X Y)).unop.hom) (by
    have : CompactSpace X.left := QuasiCompact.compactSpace_of_compactSpace X.hom
    have : CompactSpace Y.left := QuasiCompact.compactSpace_of_compactSpace Y.hom
    have : QuasiSeparatedSpace X.left := quasiSeparatedSpace_of_quasiSeparated X.hom
    have : QuasiSeparatedSpace Y.left := quasiSeparatedSpace_of_quasiSeparated Y.hom
    let : Algebra k Γ(X.left, ⊤) := inferInstanceAs (Algebra k (globalSectionsAlg X))
    let : Algebra k Γ(Y.left, ⊤) := inferInstanceAs (Algebra k (globalSectionsAlg Y))
    have hb := bijective_globalSectionsTensorDesc X.hom Y.hom rfl rfl
    have heq : ∀ t, Algebra.TensorProduct.productMap
        ((algΓ (CommRingCat.of k)).map (fst X Y)).unop.hom
        ((algΓ (CommRingCat.of k)).map (snd X Y)).unop.hom t =
        globalSectionsTensorDesc X.hom Y.hom rfl rfl t := by
      intro t
      induction t using TensorProduct.induction_on with
      | zero =>
        exact (map_zero _).trans
          (map_zero (globalSectionsTensorDesc X.hom Y.hom rfl rfl).hom).symm
      | tmul a b => exact (globalSectionsTensorDesc_tmul X.hom Y.hom rfl rfl a b).symm
      | add s t hs ht =>
        exact ((map_add _ _ _).trans (congrArg₂ _ hs ht)).trans
          (map_add (globalSectionsTensorDesc X.hom Y.hom rfl rfl).hom _ _).symm
    exact ⟨fun a b h => hb.1 (by rwa [← heq, ← heq]),
      fun c => let ⟨t, ht⟩ := hb.2 c; ⟨t, (heq t).trans ht⟩⟩)

/-- The Künneth isomorphism sends `a ⊗ b` to `pr₁^* a · pr₂^* b`. -/
@[simp]
lemma globalSectionsTensorAlgEquiv_tmul (a : globalSectionsAlg X) (b : globalSectionsAlg Y) :
    globalSectionsTensorAlgEquiv X Y (a ⊗ₜ b) =
      ((algΓ (CommRingCat.of k)).map (fst X Y)).unop.hom a *
        ((algΓ (CommRingCat.of k)).map (snd X Y)).unop.hom b := rfl

/-- **Künneth**: the global sections functor takes the product of two quasi-compact
quasi-separated schemes over `Spec k` to a product in `(CommAlgCat k)ᵒᵖ`, i.e. to the tensor
product of their global sections. -/
noncomputable def isLimitAlgΓBinaryFan :
    IsLimit (BinaryFan.mk ((algΓ (CommRingCat.of k)).map (fst X Y))
      ((algΓ (CommRingCat.of k)).map (snd X Y))) :=
  (tensorProductIsBinaryProduct ((algΓ (CommRingCat.of k)).obj X)
      ((algΓ (CommRingCat.of k)).obj Y)).ofIsoLimit
    (Cone.ext (CommAlgCat.isoMk (globalSectionsTensorAlgEquiv X Y)).op.symm (by
      rintro ⟨⟨⟩⟩
      · apply Quiver.Hom.unop_inj
        ext a
        change a ⊗ₜ[k] (1 : globalSectionsAlg Y) = (globalSectionsTensorAlgEquiv X Y).symm _
        rw [AlgEquiv.eq_symm_apply, globalSectionsTensorAlgEquiv_tmul, map_one, _root_.mul_one]
        rfl
      · apply Quiver.Hom.unop_inj
        ext b
        change (1 : globalSectionsAlg X) ⊗ₜ[k] b = (globalSectionsTensorAlgEquiv X Y).symm _
        rw [AlgEquiv.eq_symm_apply, globalSectionsTensorAlgEquiv_tmul, map_one, _root_.one_mul]
        rfl))

end Kunneth

section Functor

variable (k) in
/-- The global sections functor on schemes quasi-compact and quasi-separated over `Spec k`. -/
noncomputable abbrev qcqsGlobalSections :
    (qcqsOverField k).FullSubcategory ⥤ (CommAlgCat (CommRingCat.of k))ᵒᵖ :=
  (qcqsOverField k).ι ⋙ algΓ (CommRingCat.of k)

/-- The global sections functor on schemes quasi-compact and quasi-separated over `Spec k`
preserves the product of `X` and `Y`. -/
instance (X Y : (qcqsOverField k).FullSubcategory) :
    PreservesLimit (pair X Y) (qcqsGlobalSections k) := by
  obtain ⟨_, _⟩ := X.2
  obtain ⟨_, _⟩ := Y.2
  exact preservesLimit_of_preserves_limit_cone (tensorProductIsBinaryProduct X Y)
    ((isLimitMapConeBinaryFanEquiv _ _ _).symm (isLimitAlgΓBinaryFan X.1 Y.1))

/-- The global sections functor on schemes quasi-compact and quasi-separated over `Spec k`
preserves binary products. -/
instance : PreservesLimitsOfShape (Discrete WalkingPair) (qcqsGlobalSections k) :=
  ⟨fun {K} => preservesLimit_of_iso_diagram _ (diagramIsoPair K).symm⟩

/-- The global sections of `Spec k` over itself are the initial `k`-algebra. -/
noncomputable def isTerminalQcqsGlobalSectionsTensorUnit :
    IsTerminal ((qcqsGlobalSections k).obj (𝟙_ _)) := by
  let A := ((qcqsGlobalSections k).obj (𝟙_ _)).unop
  have : IsIso (CommAlgCat.isInitialSelf.to A) := by
    rw [ConcreteCategory.isIso_iff_bijective]
    change Function.Bijective ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫
      Scheme.Hom.appTop (𝟙 (Spec (CommRingCat.of k))))
    rw [Scheme.Hom.id_appTop, Category.comp_id]
    exact ConcreteCategory.bijective_of_isIso _
  exact (IsInitial.ofIso CommAlgCat.isInitialSelf (asIso (CommAlgCat.isInitialSelf.to A))).op

/-- The global sections functor on schemes quasi-compact and quasi-separated over `Spec k`
preserves the terminal object. -/
instance : PreservesLimit (Functor.empty.{0} _) (qcqsGlobalSections k) :=
  preservesLimit_of_preserves_limit_cone isTerminalTensorUnit
    ((isLimitMapConeEmptyConeEquiv _ _).symm isTerminalQcqsGlobalSectionsTensorUnit)

/-- The global sections functor on schemes quasi-compact and quasi-separated over `Spec k`
preserves limits of the empty diagram. -/
instance : PreservesLimitsOfShape (Discrete.{0} PEmpty) (qcqsGlobalSections k) :=
  preservesLimitsOfShape_pempty_of_preservesTerminal _

/-- The global sections functor on schemes quasi-compact and quasi-separated over `Spec k`
preserves finite products. -/
instance : PreservesFiniteProducts (qcqsGlobalSections k) :=
  .of_preserves_binary_and_terminal _

/-- The inclusion of the schemes quasi-compact and quasi-separated over `Spec k` into
`Over (Spec k)` preserves finite products. -/
instance : PreservesFiniteProducts (qcqsOverField k).ι :=
  .of_preserves_binary_and_terminal _

end Functor

section Hopf

variable {G : Scheme.{u}} (f : G ⟶ Spec (CommRingCat.of k)) [GrpObj (Over.mk f)]

/-- A group scheme over a field is quasi-separated over it, being separated (047L). -/
instance quasiSeparated_of_grpObj_overField : QuasiSeparated f := by
  have : IsSeparated f := (isSeparated_iff_isClosedImmersion_one f).2 inferInstance
  infer_instance

variable [CompactSpace G]

/-- A group scheme over `Spec k` with quasi-compact underlying space is quasi-compact over
`Spec k`. -/
instance : QuasiCompact (Over.mk f).hom := (inferInstance : QuasiCompact f)

/-- A group scheme over `Spec k` is quasi-separated over `Spec k`. -/
instance : QuasiSeparated (Over.mk f).hom := (inferInstance : QuasiSeparated f)

/-- A quasi-compact group scheme over `Spec k`, as an object of the category of schemes
quasi-compact and quasi-separated over `Spec k`. -/
noncomputable abbrev qcqsGroupObj : (qcqsOverField k).FullSubcategory :=
  ⟨Over.mk f, (inferInstance : QuasiCompact f), (inferInstance : QuasiSeparated f)⟩

attribute [local instance] Functor.Monoidal.ofChosenFiniteProducts in
/-- The group structure of a quasi-compact group scheme over `Spec k`, in the full subcategory of
schemes quasi-compact and quasi-separated over `Spec k`. -/
noncomputable instance grpObjQcqsGroupObj : GrpObj (qcqsGroupObj f) :=
  let : GrpObj ((qcqsOverField k).ι.obj (qcqsGroupObj f)) :=
    inferInstanceAs (GrpObj (Over.mk f))
  (qcqsOverField k).fullyFaithfulι.grpObj (qcqsGroupObj f)

attribute [local instance] Functor.Monoidal.ofChosenFiniteProducts in
/-- The cogroup structure on the global sections of a quasi-compact group scheme over `Spec k`,
as an object of `(CommAlgCat k)ᵒᵖ`. -/
@[sga "3 VIIB 2.1" "special case"]
noncomputable instance grpObjGlobalSectionsQcqsGroupObj :
    GrpObj ((qcqsGlobalSections k).obj (qcqsGroupObj f)) :=
  Functor.grpObjObj

/-- **The Hopf algebra of global functions of a quasi-compact group scheme over a field.**  For
a group scheme `G` over a field `k` whose underlying space is quasi-compact, `Γ(G, 𝒪_G)` is a
commutative Hopf algebra over `k`, with comultiplication, counit and antipode the pullbacks of
functions along the multiplication, the unit section and the inversion of `G`, the first read
through the Künneth isomorphism `Γ(G) ⊗[k] Γ(G) ≅ Γ(G ×_k G)`. -/
@[instance_reducible, sga "3 VIB 11.6" "special case"]
noncomputable def globalSectionsHopfAlgebra : HopfAlgebra k Γ(G, ⊤) :=
  inferInstanceAs (HopfAlgebra (CommRingCat.of k)
    ((qcqsGlobalSections k).obj (qcqsGroupObj f)).unop)

/-- The `k`-algebra structure of `Γ(G, 𝒪_G)` is that of the structure morphism of `G`. -/
lemma algebraMap_globalSectionsHopfAlgebra :
    letI := globalSectionsHopfAlgebra f
    algebraMap k Γ(G, ⊤) = (structureRingMap f).hom := rfl

/-- The antipode of `Γ(G, 𝒪_G)` is the pullback of functions along the inversion of `G`. -/
lemma antipode_globalSectionsHopfAlgebra (a : Γ(G, ⊤)) :
    letI := globalSectionsHopfAlgebra f
    HopfAlgebra.antipode k a = ι[Over.mk f].left.appTop a := rfl

/-- A fully faithful functor sends the preimage of `a ≫ g` to `g`, if `a` is the identity. -/
private theorem map_preimage_comp_of_eq_id {C D : Type*} [Category C] [Category D] {F : C ⥤ D}
    (hF : F.FullyFaithful) {X Y : C} (a : F.obj X ⟶ F.obj X) (g : F.obj X ⟶ F.obj Y)
    (h : a = 𝟙 _) : F.map (hF.preimage (a ≫ g)) = g := by
  rw [hF.map_preimage, h, Category.id_comp]

/-- The counit of `Γ(G, 𝒪_G)` is evaluation at the unit section of `G`. -/
lemma counit_globalSectionsHopfAlgebra (a : Γ(G, ⊤)) :
    letI := globalSectionsHopfAlgebra f
    Coalgebra.counit (R := k) a =
      (Scheme.ΓSpecIso (CommRingCat.of k)).hom (η[Over.mk f].left.appTop a) := by
  let : (qcqsOverField k).ι.Monoidal := Functor.Monoidal.ofChosenFiniteProducts _
  let : (qcqsGlobalSections k).Monoidal := Functor.Monoidal.ofChosenFiniteProducts _
  have h1 : (qcqsOverField k).ι.map η[qcqsGroupObj f] = η[Over.mk f] :=
    map_preimage_comp_of_eq_id _ _ _ (toUnit_unique (C := Over (Spec (CommRingCat.of k))) _ _)
  have h2 : ∀ x, (Functor.LaxMonoidal.ε (qcqsGlobalSections k)).unop.hom x =
      (Scheme.ΓSpecIso (CommRingCat.of k)).hom x := by
    intro x
    obtain ⟨r, rfl⟩ : ∃ r, (Scheme.ΓSpecIso (CommRingCat.of k)).inv r = x :=
      ⟨(Scheme.ΓSpecIso (CommRingCat.of k)).hom x,
        Iso.hom_inv_id_apply (Scheme.ΓSpecIso (CommRingCat.of k))
          (x : Γ(Spec (CommRingCat.of k), ⊤))⟩
    rw [Iso.inv_hom_id_apply]
    refine Eq.trans ?_ ((Functor.LaxMonoidal.ε (qcqsGlobalSections k)).unop.hom.commutes r)
    congr 1
  show (Functor.LaxMonoidal.ε (qcqsGlobalSections k) ≫
    (algΓ (CommRingCat.of k)).map ((qcqsOverField k).ι.map η[qcqsGroupObj f])).unop.hom a = _
  rw [h1]
  exact h2 _

/-- The comultiplication of `Γ(G, 𝒪_G)` is the pullback of functions along the multiplication
of `G`, read through the Künneth isomorphism `Γ(G) ⊗[k] Γ(G) ≅ Γ(G ×_k G)`. -/
lemma globalSectionsTensorAlgEquiv_comul (a : Γ(G, ⊤)) :
    letI := globalSectionsHopfAlgebra f
    globalSectionsTensorAlgEquiv (Over.mk f) (Over.mk f)
        (Coalgebra.comul (R := k) a : Γ(G, ⊤) ⊗[k] Γ(G, ⊤)) =
      μ[Over.mk f].left.appTop a := by
  let : (qcqsOverField k).ι.Monoidal := Functor.Monoidal.ofChosenFiniteProducts _
  let : (qcqsGlobalSections k).Monoidal := Functor.Monoidal.ofChosenFiniteProducts _
  have h1 : (qcqsOverField k).ι.map μ[qcqsGroupObj f] = μ[Over.mk f] :=
    map_preimage_comp_of_eq_id _ _ _ (by
      rw [Functor.OplaxMonoidal.δ_of_cartesianMonoidalCategory]
      exact lift_fst_snd)
  let P := CartesianMonoidalCategory.prodComparisonIso (qcqsGlobalSections k)
    (qcqsGroupObj f) (qcqsGroupObj f)
  have h2 : ∀ t, globalSectionsTensorAlgEquiv (Over.mk f) (Over.mk f) t = P.hom.unop.hom t := by
    intro t
    induction t using TensorProduct.induction_on with
    | zero => exact (map_zero _).trans (map_zero P.hom.unop.hom).symm
    | tmul x y => rfl
    | add s t hs ht =>
      exact ((map_add _ _ _).trans (congrArg₂ _ hs ht)).trans (map_add P.hom.unop.hom _ _).symm
  show globalSectionsTensorAlgEquiv (Over.mk f) (Over.mk f)
    ((Functor.LaxMonoidal.μ (qcqsGlobalSections k) (qcqsGroupObj f) (qcqsGroupObj f) ≫
      (algΓ (CommRingCat.of k)).map ((qcqsOverField k).ι.map μ[qcqsGroupObj f])).unop.hom a) = _
  rw [h1, Functor.Monoidal.μ_of_cartesianMonoidalCategory, h2]
  show (P.hom ≫ P.inv ≫ (algΓ (CommRingCat.of k)).map μ[Over.mk f]).unop.hom a = _
  rw [P.hom_inv_id_assoc]
  rfl

end Hopf

end AlgebraicGeometry
