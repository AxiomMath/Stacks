module

public import Mathlib.CategoryTheory.Limits.Fubini
public import StacksCore.Tactic.StacksAttribute

/-!
# Iterated colimits and limits under pointwise existence

Let `M : I × J ⥤ C` be a functor and assume that for every `i` the colimit
`M_{i,∞} = colim_j M_{i,j}` exists. Then the functor `M_{-,∞} : i ↦ M_{i,∞}` has a colimit if
and only if `M` has a colimit, and when they exist the two colimits agree. Consequently
`colim_i colim_j M_{i,j} = colim_{(i,j)} M_{i,j} = colim_j colim_i M_{i,j}` whenever the
partial colimits exist in both directions. The same holds for limits. This is
[Stacks, Tag 002M].

Mathlib's `Mathlib.CategoryTheory.Limits.Fubini` states the isomorphisms under the global
hypothesis `HasColimitsOfShape J C`, and only shows that the colimit of `M` exists when the
iterated colimit does. Here only the colimits `colim_j M_{i,j}` are assumed to exist, and both
directions are proved.

## Main definitions

* `CategoryTheory.Limits.DiagramOfCocones.mkOfHasColimit`: for `F : I ⥤ J ⥤ C` with
  `∀ i, HasColimit (F.obj i)`, the colimit cocones of the `F.obj i` and the maps between them.
* `CategoryTheory.Limits.pointwiseColim F`: the functor `i ↦ colimit (F.obj i)`.
* `CategoryTheory.Limits.DiagramOfCones.mkOfHasLimit`, `CategoryTheory.Limits.pointwiseLim F`:
  the same for limits.

## Main results

* `CategoryTheory.Limits.hasColimit_iff_hasColimit_pointwiseColim_curry`:
  `HasColimit G ↔ HasColimit (pointwiseColim (curry.obj G))`.
* `CategoryTheory.Limits.colimitIsoColimitPointwiseColimCurry`: the two colimits agree.
* `CategoryTheory.Limits.hasColimit_pointwiseColim_curry_swap_iff` and
  `CategoryTheory.Limits.pointwiseColimCurrySwapIso`: `colim_j colim_i = colim_i colim_j`.
* The corresponding statements for limits.
-/

@[expose] public section

open CategoryTheory Functor

namespace CategoryTheory.Limits

variable {I J C : Type*} [Category* I] [Category* J] [Category* C]

section Colimits

variable (F : I ⥤ J ⥤ C)

/-- For `F : I ⥤ J ⥤ C` such that each `F.obj i` has a colimit, the colimit cocones of the
`F.obj i` together with the induced maps between their points. -/
@[simps]
noncomputable def DiagramOfCocones.mkOfHasColimit [∀ i, HasColimit (F.obj i)] :
    DiagramOfCocones F where
  obj i := colimit.cocone (F.obj i)
  map f := { hom := colimMap (F.map f) }
  id i := by dsimp; ext; simp
  comp f g := by dsimp; ext; simp

/-- The functor `i ↦ colim_j F(i, j)`, defined as soon as each of these colimits exists. -/
noncomputable abbrev pointwiseColim [∀ i, HasColimit (F.obj i)] : I ⥤ C :=
  (DiagramOfCocones.mkOfHasColimit F).coconePoints

variable {F}

/-- The legs of the cocones `D.obj i` of a diagram of cocones, as a natural transformation from
`uncurry.obj F` to the cocone points of `D` composed with the first projection. -/
@[simps]
def DiagramOfCocones.uncurryToCoconePoints (D : DiagramOfCocones F) :
    uncurry.obj F ⟶ Prod.fst I J ⋙ D.coconePoints where
  app p := (D.obj p.1).ι.app p.2
  naturality := by
    rintro ⟨i, j⟩ ⟨i', j'⟩ ⟨f, g⟩
    have h₁ := (D.obj i').ι.naturality g
    have h₂ := (D.map f).w j
    dsimp at h₁ h₂ ⊢
    simp only [Category.comp_id] at h₁
    exact (Category.assoc _ _ _).trans ((whisker_eq _ h₁).trans h₂.symm)

/-- Given a diagram of cocones `D` over the `F.obj i` and a cocone `s` over its cocone points,
the cocone over `uncurry.obj F` with legs `D.obj i` followed by `s`. -/
@[simps!]
def DiagramOfCocones.coconeUncurry (D : DiagramOfCocones F) (s : Cocone D.coconePoints) :
    Cocone (uncurry.obj F) :=
  (Cocone.precompose D.uncurryToCoconePoints).obj (s.whisker (Prod.fst I J))

/-- Applying `coconeOfCoconeUncurry` to `D.coconeUncurry s` gives back `s`. -/
def DiagramOfCocones.coconeOfCoconeUncurryCoconeUncurryIso (D : DiagramOfCocones F)
    (Q : ∀ i, IsColimit (D.obj i)) (s : Cocone D.coconePoints) :
    coconeOfCoconeUncurry Q (D.coconeUncurry s) ≅ s :=
  Cocone.ext (Iso.refl _) fun i => (Q i).hom_ext fun j =>
    (whisker_eq _ (Category.comp_id _)).trans ((Q i).fac _ j)

/-- If `s` is a colimit cocone over the cocone points of a diagram of colimit cocones, then
`D.coconeUncurry s` is a colimit cocone over `uncurry.obj F`. -/
def DiagramOfCocones.isColimitCoconeUncurry (D : DiagramOfCocones F)
    (Q : ∀ i, IsColimit (D.obj i)) {s : Cocone D.coconePoints} (hs : IsColimit s) :
    IsColimit (D.coconeUncurry s) :=
  IsColimit.ofCoconeUncurry Q
    (hs.ofIsoColimit (D.coconeOfCoconeUncurryCoconeUncurryIso Q s).symm)

variable (F)

/-- **Stacks 002M**, curried form: if each `F.obj i` has a colimit, then `uncurry.obj F` has a
colimit if and only if `i ↦ colim_j F(i, j)` has one. -/
@[stacks 002M "curried form: given each colim_j, total colimit exists iff iterated one does"]
theorem hasColimit_uncurry_iff [∀ i, HasColimit (F.obj i)] :
    HasColimit (uncurry.obj F) ↔ HasColimit (pointwiseColim F) := by
  have Q : ∀ i, IsColimit ((DiagramOfCocones.mkOfHasColimit F).obj i) :=
    fun i => colimit.isColimit _
  constructor
  · intro _
    exact HasColimit.mk ⟨_, coconeOfCoconeUncurryIsColimit Q (colimit.isColimit _)⟩
  · intro _
    exact HasColimit.mk ⟨_, DiagramOfCocones.isColimitCoconeUncurry _ Q (colimit.isColimit _)⟩

/-- **Stacks 002M**, curried form: when they exist, the colimit of `uncurry.obj F` is the
colimit of `i ↦ colim_j F(i, j)`. -/
@[stacks 002M "curried form: the total and iterated colimits agree"]
noncomputable def colimitUncurryIsoColimitPointwiseColim [∀ i, HasColimit (F.obj i)]
    [HasColimit (uncurry.obj F)] [HasColimit (pointwiseColim F)] :
    colimit (uncurry.obj F) ≅ colimit (pointwiseColim F) :=
  IsColimit.coconePointUniqueUpToIso
    (coconeOfCoconeUncurryIsColimit (D := DiagramOfCocones.mkOfHasColimit F)
      (fun _ => colimit.isColimit _) (colimit.isColimit _))
    (colimit.isColimit _)

variable (G : I × J ⥤ C)

/-- **Stacks 002M**: for `G : I × J ⥤ C` such that `colim_j G(i, j)` exists for every `i`, the
functor `G` has a colimit if and only if `i ↦ colim_j G(i, j)` has one. -/
@[stacks 002M "given each colim_j M_{i,j}, M has a colimit iff M_{-,∞} has one"]
theorem hasColimit_iff_hasColimit_pointwiseColim_curry
    [∀ i, HasColimit ((curry.obj G).obj i)] :
    HasColimit G ↔ HasColimit (pointwiseColim (curry.obj G)) := by
  rw [← hasColimit_uncurry_iff]
  have e : G ≅ uncurry.obj (curry.obj G) := currying.symm.unitIso.app G
  exact ⟨fun _ => hasColimit_of_iso e.symm, fun _ => hasColimit_of_iso e⟩

/-- **Stacks 002M**: when they exist, `colim_{(i,j)} G(i, j) ≅ colim_i colim_j G(i, j)`. -/
@[stacks 002M "when they exist, the colimits of M and of M_{-,∞} agree"]
noncomputable def colimitIsoColimitPointwiseColimCurry [∀ i, HasColimit ((curry.obj G).obj i)]
    [HasColimit G] [HasColimit (pointwiseColim (curry.obj G))] :
    colimit G ≅ colimit (pointwiseColim (curry.obj G)) :=
  haveI : HasColimit (uncurry.obj (curry.obj G)) :=
    hasColimit_of_iso (F := G) (G := uncurry.obj (curry.obj G))
      (currying.symm.unitIso.app G).symm
  HasColimit.isoOfNatIso (F := G) (G := uncurry.obj (curry.obj G))
    (currying.symm.unitIso.app G) ≪≫
    colimitUncurryIsoColimitPointwiseColim (curry.obj G)

/-- **Stacks 002M**: if `colim_j G(i, j)` exists for every `i` and `colim_i G(i, j)` exists for
every `j`, then `colim_i colim_j G(i, j)` exists if and only if `colim_j colim_i G(i, j)` does. -/
@[stacks 002M "given colimits in both variables, colim_i colim_j exists iff colim_j colim_i does"]
theorem hasColimit_pointwiseColim_curry_swap_iff [∀ i, HasColimit ((curry.obj G).obj i)]
    [∀ j, HasColimit ((curry.obj (Prod.swap J I ⋙ G)).obj j)] :
    HasColimit (pointwiseColim (curry.obj (Prod.swap J I ⋙ G))) ↔
      HasColimit (pointwiseColim (curry.obj G)) := by
  rw [← hasColimit_iff_hasColimit_pointwiseColim_curry,
    ← hasColimit_iff_hasColimit_pointwiseColim_curry]
  exact hasColimit_equivalence_comp_iff (Prod.braiding J I)

/-- **Stacks 002M**: when they exist, `colim_j colim_i G(i, j) ≅ colim_i colim_j G(i, j)`. -/
@[stacks 002M "colim_j colim_i = colim_i colim_j, given colimits in both variables"]
noncomputable def pointwiseColimCurrySwapIso [∀ i, HasColimit ((curry.obj G).obj i)]
    [∀ j, HasColimit ((curry.obj (Prod.swap J I ⋙ G)).obj j)]
    [HasColimit (pointwiseColim (curry.obj G))]
    [HasColimit (pointwiseColim (curry.obj (Prod.swap J I ⋙ G)))] :
    colimit (pointwiseColim (curry.obj (Prod.swap J I ⋙ G))) ≅
      colimit (pointwiseColim (curry.obj G)) :=
  haveI : HasColimit G := (hasColimit_iff_hasColimit_pointwiseColim_curry G).2 inferInstance
  haveI : HasColimit (Prod.swap J I ⋙ G) :=
    (hasColimit_iff_hasColimit_pointwiseColim_curry _).2 inferInstance
  (colimitIsoColimitPointwiseColimCurry (Prod.swap J I ⋙ G)).symm ≪≫
    HasColimit.isoOfEquivalence (Prod.braiding J I) (Iso.refl _) ≪≫
    colimitIsoColimitPointwiseColimCurry G

end Colimits

section Limits

variable (F : I ⥤ J ⥤ C)

/-- For `F : I ⥤ J ⥤ C` such that each `F.obj i` has a limit, the limit cones of the `F.obj i`
together with the induced maps between their points. -/
@[simps]
noncomputable def DiagramOfCones.mkOfHasLimit [∀ i, HasLimit (F.obj i)] :
    DiagramOfCones F where
  obj i := limit.cone (F.obj i)
  map f := { hom := limMap (F.map f) }
  id i := by dsimp; ext; simp
  comp f g := by dsimp; ext; simp

/-- The functor `i ↦ lim_j F(i, j)`, defined as soon as each of these limits exists. -/
noncomputable abbrev pointwiseLim [∀ i, HasLimit (F.obj i)] : I ⥤ C :=
  (DiagramOfCones.mkOfHasLimit F).conePoints

variable {F}

/-- The legs of the cones `D.obj i` of a diagram of cones, as a natural transformation from the
cone points of `D` composed with the first projection to `uncurry.obj F`. -/
@[simps]
def DiagramOfCones.conePointsToUncurry (D : DiagramOfCones F) :
    Prod.fst I J ⋙ D.conePoints ⟶ uncurry.obj F where
  app p := (D.obj p.1).π.app p.2
  naturality := by
    rintro ⟨i, j⟩ ⟨i', j'⟩ ⟨f, g⟩
    have h₁ := (D.obj i').π.naturality g
    have h₂ := (D.map f).w j
    dsimp at h₁ h₂ ⊢
    simp only [Category.id_comp] at h₁
    exact (whisker_eq _ h₁).trans
      ((Category.assoc _ _ _).symm.trans ((eq_whisker h₂ _).trans (Category.assoc _ _ _)))

/-- Given a diagram of cones `D` over the `F.obj i` and a cone `s` over its cone points, the
cone over `uncurry.obj F` with legs `s` followed by `D.obj i`. -/
@[simps!]
def DiagramOfCones.coneUncurry (D : DiagramOfCones F) (s : Cone D.conePoints) :
    Cone (uncurry.obj F) :=
  (Cone.postcompose D.conePointsToUncurry).obj (s.whisker (Prod.fst I J))

/-- Applying `coneOfConeUncurry` to `D.coneUncurry s` gives back `s`. -/
def DiagramOfCones.coneOfConeUncurryConeUncurryIso (D : DiagramOfCones F)
    (Q : ∀ i, IsLimit (D.obj i)) (s : Cone D.conePoints) :
    coneOfConeUncurry Q (D.coneUncurry s) ≅ s :=
  Cone.ext (Iso.refl _) fun i => (Q i).hom_ext fun j =>
    ((Q i).fac _ j).trans (eq_whisker (Category.id_comp _).symm _)

/-- If `s` is a limit cone over the cone points of a diagram of limit cones, then
`D.coneUncurry s` is a limit cone over `uncurry.obj F`. -/
def DiagramOfCones.isLimitConeUncurry (D : DiagramOfCones F)
    (Q : ∀ i, IsLimit (D.obj i)) {s : Cone D.conePoints} (hs : IsLimit s) :
    IsLimit (D.coneUncurry s) :=
  IsLimit.ofConeOfConeUncurry Q
    (hs.ofIsoLimit (D.coneOfConeUncurryConeUncurryIso Q s).symm)

variable (F)

/-- **Stacks 002M**, curried form for limits: if each `F.obj i` has a limit, then
`uncurry.obj F` has a limit if and only if `i ↦ lim_j F(i, j)` has one. -/
@[stacks 002M "limits, curried form: given each lim_j, total limit exists iff iterated one does"]
theorem hasLimit_uncurry_iff [∀ i, HasLimit (F.obj i)] :
    HasLimit (uncurry.obj F) ↔ HasLimit (pointwiseLim F) := by
  have Q : ∀ i, IsLimit ((DiagramOfCones.mkOfHasLimit F).obj i) :=
    fun i => limit.isLimit _
  constructor
  · intro _
    exact HasLimit.mk ⟨_, coneOfConeUncurryIsLimit Q (limit.isLimit _)⟩
  · intro _
    exact HasLimit.mk ⟨_, DiagramOfCones.isLimitConeUncurry _ Q (limit.isLimit _)⟩

/-- **Stacks 002M**, curried form for limits: when they exist, the limit of `uncurry.obj F` is
the limit of `i ↦ lim_j F(i, j)`. -/
@[stacks 002M "limits, curried form: the total and iterated limits agree"]
noncomputable def limitUncurryIsoLimitPointwiseLim [∀ i, HasLimit (F.obj i)]
    [HasLimit (uncurry.obj F)] [HasLimit (pointwiseLim F)] :
    limit (uncurry.obj F) ≅ limit (pointwiseLim F) :=
  IsLimit.conePointUniqueUpToIso
    (coneOfConeUncurryIsLimit (D := DiagramOfCones.mkOfHasLimit F)
      (fun _ => limit.isLimit _) (limit.isLimit _))
    (limit.isLimit _)

variable (G : I × J ⥤ C)

/-- **Stacks 002M** for limits: for `G : I × J ⥤ C` such that `lim_j G(i, j)` exists for every
`i`, the functor `G` has a limit if and only if `i ↦ lim_j G(i, j)` has one. -/
@[stacks 002M "limits: given each lim_j M_{i,j}, M has a limit iff M_{-,∞} has one"]
theorem hasLimit_iff_hasLimit_pointwiseLim_curry [∀ i, HasLimit ((curry.obj G).obj i)] :
    HasLimit G ↔ HasLimit (pointwiseLim (curry.obj G)) := by
  rw [← hasLimit_uncurry_iff]
  have e : G ≅ uncurry.obj (curry.obj G) := currying.symm.unitIso.app G
  exact ⟨fun _ => hasLimit_of_iso e, fun _ => hasLimit_of_iso e.symm⟩

/-- **Stacks 002M** for limits: when they exist, `lim_{(i,j)} G(i, j) ≅ lim_i lim_j G(i, j)`. -/
@[stacks 002M "limits: when they exist, the limits of M and of M_{-,∞} agree"]
noncomputable def limitIsoLimitPointwiseLimCurry [∀ i, HasLimit ((curry.obj G).obj i)]
    [HasLimit G] [HasLimit (pointwiseLim (curry.obj G))] :
    limit G ≅ limit (pointwiseLim (curry.obj G)) :=
  haveI : HasLimit (uncurry.obj (curry.obj G)) :=
    hasLimit_of_iso (F := G) (G := uncurry.obj (curry.obj G)) (currying.symm.unitIso.app G)
  HasLimit.isoOfNatIso (F := G) (G := uncurry.obj (curry.obj G))
    (currying.symm.unitIso.app G) ≪≫
    limitUncurryIsoLimitPointwiseLim (curry.obj G)

/-- **Stacks 002M** for limits: if `lim_j G(i, j)` exists for every `i` and `lim_i G(i, j)`
exists for every `j`, then `lim_i lim_j G(i, j)` exists if and only if `lim_j lim_i G(i, j)`
does. -/
@[stacks 002M "limits: given limits in both variables, lim_i lim_j exists iff lim_j lim_i does"]
theorem hasLimit_pointwiseLim_curry_swap_iff [∀ i, HasLimit ((curry.obj G).obj i)]
    [∀ j, HasLimit ((curry.obj (Prod.swap J I ⋙ G)).obj j)] :
    HasLimit (pointwiseLim (curry.obj (Prod.swap J I ⋙ G))) ↔
      HasLimit (pointwiseLim (curry.obj G)) := by
  rw [← hasLimit_iff_hasLimit_pointwiseLim_curry, ← hasLimit_iff_hasLimit_pointwiseLim_curry]
  exact hasLimit_equivalence_comp_iff (Prod.braiding J I)

/-- **Stacks 002M** for limits: when they exist, `lim_j lim_i G(i, j) ≅ lim_i lim_j G(i, j)`. -/
@[stacks 002M "limits: lim_j lim_i = lim_i lim_j, given limits in both variables"]
noncomputable def pointwiseLimCurrySwapIso [∀ i, HasLimit ((curry.obj G).obj i)]
    [∀ j, HasLimit ((curry.obj (Prod.swap J I ⋙ G)).obj j)]
    [HasLimit (pointwiseLim (curry.obj G))]
    [HasLimit (pointwiseLim (curry.obj (Prod.swap J I ⋙ G)))] :
    limit (pointwiseLim (curry.obj (Prod.swap J I ⋙ G))) ≅
      limit (pointwiseLim (curry.obj G)) :=
  haveI : HasLimit G := (hasLimit_iff_hasLimit_pointwiseLim_curry G).2 inferInstance
  haveI : HasLimit (Prod.swap J I ⋙ G) :=
    (hasLimit_iff_hasLimit_pointwiseLim_curry _).2 inferInstance
  (limitIsoLimitPointwiseLimCurry (Prod.swap J I ⋙ G)).symm ≪≫
    HasLimit.isoOfEquivalence (Prod.braiding J I) (Iso.refl _) ≪≫
    limitIsoLimitPointwiseLimCurry G

end Limits

end CategoryTheory.Limits
