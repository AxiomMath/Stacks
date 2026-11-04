module

public import StacksFrontier.AlgebraicGeometry.Quot.ZarConeRelHomIsSheaf
public import StacksFrontier.AlgebraicGeometry.Quot.PicardDescent.BaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.SpacesEtaleModuleHomSheaf
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartReadingInternalHom
public import StacksFrontier.AlgebraicGeometry.Spaces.ClopenLiftOverHenselianPair
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartBranchCodimension
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.QuasicoherentAbelian

/-!
# The relative Hom presheaves of modules along the Zariski cone are sheaves

Let `f : X ⟶ Y` be a morphism of algebraic spaces, `T` a test scheme over `Y` and
`h₀ : Z₀ ⟶ T` a morphism of the site.  Along the cone `AlgebraicGeometry.Space.zarCone f T h₀`
of the base changes `X_{T_W}` over the opens `W` of `Z₀`, the relative Hom presheaves
`W ↦ Hom(N|_{X_{T_W}}, N'|_{X_{T_W}})` of two modules on `X_{T_{Z₀}}` are sheaves on the opens of
`Z₀` (`AlgebraicGeometry.Space.zarConeRelHomIsSheaf`).

This is étale descent of morphisms of modules along the family `X_{T_{V i}} ⟶ X_{T_U}` for opens
`V i` covering `U`, in the form `AlgebraicGeometry.Space.existsUnique_restrictForm_eq`.  Two
inputs are proved here:

* the family is an étale covering (`AlgebraicGeometry.Space.isEtaleCovering_zarSpaces_map`): its
  members are base changes of the open immersions `T_{V i} ⟶ T_U`, and a point of `X_{T_U}` lies
  over a point of `T_U`, which lies in some `V i`;
* `X_{T_{V i ⊓ V k}}` is the fibre product of `X_{T_{V i}}` and `X_{T_{V k}}` over `X_{T_U}`
  (`AlgebraicGeometry.Space.isPullback_zarSpaces_map_inf`), because base change preserves the
  cartesian square of the opens `V i ⊓ V k ⟶ V i, V k ⟶ U`.  So the agreement of two sections on
  `V i ⊓ V k` is the agreement on the pairwise fibre product that descent asks for.

The relative Hom presheaves are those of the inverse image of Stacks 03LU
(`AlgebraicGeometry.Space.modulePullbackData`), whose transition maps are the restricted readings
`AlgebraicGeometry.Space.QuasiCoherentDescent.restrictForm`; the datum
`AlgebraicGeometry.Space.modulePullbackDataTopos` of the statement is the same datum with its
inverse images replaced by equal functors, and the sheaf property transfers along that
(`CategoryTheory.PullbackData.relHomOpens_isSheaf_ofEq`).

Nothing here is registered.

## References

* [Stacks Project, Tag 04W6](https://stacks.math.columbia.edu/tag/04W6)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

/-! ### Transport of the sheaf property along an equality of inverse images -/

namespace CategoryTheory.PullbackData

universe v₀ v₁ u₁ v₂ u₂

variable {X₀ : Type v₀} [TopologicalSpace X₀]
  {A : Type u₁} [Category.{v₁} A] {M : A → Type u₂} [∀ a, Category.{v₂} (M a)]
  [∀ a, Preadditive (M a)]

omit [∀ a, Preadditive (M a)] in
/-- The relative Hom maps of a datum with its inverse images replaced by the same functors are
the relative Hom maps of the datum. -/
theorem relHomMap_ofEq_self (P : PullbackData A M)
    (h : ∀ {a b : A} (f : a ⟶ b), P.pull f = P.pull f) {I : Type*} [Category* I] {π : I ⥤ A}
    {a₀ : A} (κ : ConeTo π a₀) (N N' : M a₀) {j i : I} (g : j ⟶ i)
    (α : P.relHomObj κ N N' i) :
    (P.ofEq P.pull h).relHomMap κ N N' g α = P.relHomMap κ N N' g α := by
  simp only [relHomMap, Functor.conjHom, triangle, ofEq, Iso.trans_hom, Iso.trans_inv,
    eqToIso_refl, Iso.refl_hom, Iso.refl_inv, NatTrans.comp_app,
    Category.id_comp, Category.comp_id, Category.assoc]

/-- **The sheaf property of the relative Hom presheaves transfers along an equality of the
inverse images.** -/
theorem relHomOpens_isSheaf_ofEq (P : PullbackData A M)
    [∀ {a b : A} (f : a ⟶ b), (P.pull f).Additive] (hP : P.IsCoherent)
    (pull : ∀ {a b : A}, (a ⟶ b) → (M b ⥤ M a)) (hpull : ∀ {a b : A} (f : a ⟶ b), pull f = P.pull f)
    [∀ {a b : A} (f : a ⟶ b), (pull f).Additive] (hP' : (P.ofEq pull hpull).IsCoherent)
    {π : Opens X₀ ⥤ A} {a₀ : A} (κ : ConeTo π a₀) (N N' : M a₀)
    (hsh : (P.relHomOpens hP κ N N').IsSheaf) :
    ((P.ofEq pull hpull).relHomOpens hP' κ N N').IsSheaf := by
  obtain rfl : @pull = @P.pull := by
    funext a b f
    exact hpull f
  have hres : ∀ {W W' : Opens X₀} (h : W' ≤ W) (x : (P.relHomOpens hP κ N N').obj W),
      ((P.ofEq P.pull hpull).relHomOpens hP' κ N N').res h x =
        (P.relHomOpens hP κ N N').res h x :=
    fun h x => relHomMap_ofEq_self P hpull κ N N' (homOfLE h) x
  intro U ι V hV hsup s hs
  obtain ⟨x, hx, hu⟩ := hsh U V hV hsup s fun i k =>
    (hres _ _).symm.trans ((hs i k).trans (hres _ _))
  exact ⟨x, fun i => (hres _ x).trans (hx i),
    fun y hy => hu y fun i => (hres _ y).symm.trans (hy i)⟩

end CategoryTheory.PullbackData

/-! ### The cartesian square of two opens -/

namespace AlgebraicGeometry.BigFppfOver

universe u

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **The square of the intersection of two opens is cartesian in the big fppf site.** -/
theorem isPullback_openSubHomOfLE_inf (Z : BigFppfOver B S hS) {U V W : Z.left.obj.Opens}
    (hU : U ≤ W) (hV : V ≤ W) :
    IsPullback (openSubHomOfLE B S hS Z (inf_le_left : U ⊓ V ≤ U))
      (openSubHomOfLE B S hS Z (inf_le_right : U ⊓ V ≤ V))
      (openSubHomOfLE B S hS Z hU) (openSubHomOfLE B S hS Z hV) := by
  have : (BigFppfOver.toScheme B S hS).Faithful := by
    dsimp [BigFppfOver.toScheme]
    infer_instance
  have : ReflectsLimitsOfShape WalkingCospan (BigFppfOver.toScheme B S hS) := by
    dsimp [BigFppfOver.toScheme, BigFppfOver.forget]
    infer_instance
  exact IsPullback.of_map_of_faithful (BigFppfOver.toScheme B S hS)
    (isPullback_opens_inf_le (X := Z.left.obj) hU hV)

end AlgebraicGeometry.BigFppfOver

namespace AlgebraicGeometry.Space

universe u

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-! ### The points of a covering family of opens -/

/-- **The opens of a covering family cover the points of the represented presheaf.** -/
theorem exists_mem_range_pointsMap_openSubHomOfLE (Z : BigFppfOver B S hS)
    {U : Z.left.obj.Opens} {ι : Type*} (V : ι → Z.left.obj.Opens) (hV : ∀ i, V i ≤ U)
    (hsup : iSup V = U) (p : points B S hS (yoneda.obj (BigFppfOver.openSubObj B S hS Z U))) :
    ∃ i, p ∈ Set.range (pointsMap B S hS _
      (yoneda.map (BigFppfOver.openSubHomOfLE B S hS Z (hV i)))) := by
  set a : U := pointsEquivScheme B S hS (BigFppfOver.openSubObj B S hS Z U) p with ha
  have hmem : a.1 ∈ iSup V := hsup.symm ▸ a.2
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 hmem
  refine ⟨i, (pointsEquivScheme B S hS (BigFppfOver.openSubObj B S hS Z (V i))).symm ⟨a.1, hi⟩,
    ?_⟩
  exact (ChartBranch.pointsEquivScheme_symm_pointsMap B S hS
    (BigFppfOver.openSubHomOfLE B S hS Z (hV i)) ⟨a.1, hi⟩).trans
    ((Equiv.symm_apply_eq _).2
      (ha ▸ Subtype.ext (Scheme.homOfLE_apply (X := Z.left.obj) (hV i) ⟨a.1, hi⟩)))

variable {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) (T : SchemesOver Y)
  {Z₀ : BigFppfOver B S hS} (h₀ : Z₀ ⟶ T.left)

/-! ### The base changes over a covering family of opens -/

/-- **The base changes over a covering family of opens form an étale covering.** -/
theorem isEtaleCovering_zarSpaces_map {U : Z₀.left.obj.Opens} {ι : Type*}
    (V : ι → Z₀.left.obj.Opens) (hV : ∀ i, V i ≤ U) (hsup : iSup V = U) :
    IsEtaleCovering B S hS (fun i => ((zarSpaces f T h₀).obj (V i)).1)
      (fun i => ((zarSpaces f T h₀).map (homOfLE (hV i))).hom) where
  target_isAlgebraicSpace := ((zarSpaces f T h₀).obj U).2
  source_isAlgebraicSpace i := ((zarSpaces f T h₀).obj (V i)).2
  etale i := isEtale_zarSpaces_map f T h₀ (homOfLE (hV i))
  jointly_surjective := by
    refine Set.eq_univ_of_forall fun x => Set.mem_iUnion.2 ?_
    obtain ⟨i, hi⟩ := exists_mem_range_pointsMap_openSubHomOfLE Z₀ V hV hsup
      (pointsMap B S hS _ (baseChangeInclusion f ((zarOpensTest T h₀).obj U)).hom x)
    refine ⟨i, ?_⟩
    have hsq := (AlgebraicSpaces.isPullback_hom B S hS
      (isPullback_baseChangeMap f ((zarOpensTest T h₀).map (homOfLE (hV i))))).flip
    exact (preimage_range_pointsMap_of_isPullback B S hS hsq).subset hi

/-- **The base change over the intersection of two opens is the fibre product of the base
changes.** -/
theorem isPullback_zarSpaces_map_inf {U V W : Z₀.left.obj.Opens} (hU : U ≤ W) (hV : V ≤ W) :
    IsPullback ((zarSpaces f T h₀).map (homOfLE (inf_le_left : U ⊓ V ≤ U)))
      ((zarSpaces f T h₀).map (homOfLE (inf_le_right : U ⊓ V ≤ V)))
      ((zarSpaces f T h₀).map (homOfLE hU)) ((zarSpaces f T h₀).map (homOfLE hV)) :=
  isPullback_baseChangeMap_of_isPullback f
    (β₁ := (zarOpensTest T h₀).map (homOfLE (inf_le_left : U ⊓ V ≤ U)))
    (β₂ := (zarOpensTest T h₀).map (homOfLE (inf_le_right : U ⊓ V ≤ V)))
    (g₁ := (zarOpensTest T h₀).map (homOfLE hU)) (g₂ := (zarOpensTest T h₀).map (homOfLE hV))
    (BigFppfOver.isPullback_openSubHomOfLE_inf Z₀ hU hV)

/-! ### The sheaf property -/

/-- The inverse images of the datum of Stacks 03LU are additive. -/
theorem modulePullbackData_pull_additive {X' Y' : AlgebraicSpaces B S hS} (g : X' ⟶ Y') :
    ((modulePullbackData B S hS).pull g).Additive :=
  modulePullback_additive g

attribute [local instance] modulePullbackData_pull_additive

attribute [local irreducible] modulePullback

/-- The comparison triangles of the datum of Stacks 03LU are
`AlgebraicGeometry.Space.modulePullbackTriangle`. -/
theorem modulePullbackData_triangle {X' Y' Z' : AlgebraicSpaces B S hS} {a : X' ⟶ Y'}
    {b : Y' ⟶ Z'} {k : X' ⟶ Z'} (hk : a ≫ b = k) :
    (modulePullbackData B S hS).triangle hk = modulePullbackTriangle B S hS hk :=
  rfl

/-- The transition maps of the relative Hom presheaves of the inverse image of Stacks 03LU along
the Zariski cone are the restricted readings. -/
theorem modulePullbackData_relHomOpens_zarCone_res
    (N N' : Modules.{u, u} B S hS (baseChangeSpace f (restrictTest T h₀)).1
      (baseChangeSpace f (restrictTest T h₀)).2)
    {W W' : Z₀.left.obj.Opens} (h : W' ≤ W)
    (x : (modulePullbackData B S hS).relHomObj (zarCone f T h₀) N N' W) :
    ((modulePullbackData B S hS).relHomOpens (modulePullbackData_isCoherent B S hS)
        (zarCone f T h₀) N N').res h x =
      QuasiCoherentDescent.restrictForm B S hS ((zarSpaces f T h₀).map (homOfLE h))
        ((zarCone f T h₀).leg W) ((zarCone f T h₀).leg W') ((zarCone f T h₀).w (homOfLE h)) x := by
  rw [PullbackData.relHomOpens_res, PullbackData.relHomMap, modulePullbackData_triangle]
  exact conjHom_modulePullbackTriangle_eq_restrictForm B S hS ((zarCone f T h₀).w (homOfLE h)) x

/-- **The relative Hom presheaves of the inverse image of Stacks 03LU along the Zariski cone are
sheaves.** -/
theorem modulePullbackData_relHomOpens_zarCone_isSheaf
    (N N' : Modules.{u, u} B S hS (baseChangeSpace f (restrictTest T h₀)).1
      (baseChangeSpace f (restrictTest T h₀)).2) :
    ((modulePullbackData B S hS).relHomOpens (modulePullbackData_isCoherent B S hS)
      (zarCone f T h₀) N N').IsSheaf := by
  intro U ι V hV hsup s hs
  have hres := @modulePullbackData_relHomOpens_zarCone_res _ _ _ _ _ f T _ h₀ N N'
  have hx : ∀ i j (h : QuasiCoherentDescent.pairSnd B S hS (fun i => (zarSpaces f T h₀).obj (V i))
        (fun i => (zarSpaces f T h₀).map (homOfLE (hV i))) i j ≫ (zarCone f T h₀).leg (V j) =
      QuasiCoherentDescent.pairFst B S hS (fun i => (zarSpaces f T h₀).obj (V i))
        (fun i => (zarSpaces f T h₀).map (homOfLE (hV i))) i j ≫ (zarCone f T h₀).leg (V i)),
      QuasiCoherentDescent.restrictForm B S hS
          (QuasiCoherentDescent.pairFst B S hS (fun i => (zarSpaces f T h₀).obj (V i))
            (fun i => (zarSpaces f T h₀).map (homOfLE (hV i))) i j)
          ((zarCone f T h₀).leg (V i)) _ rfl (s i) =
        QuasiCoherentDescent.restrictForm B S hS
          (QuasiCoherentDescent.pairSnd B S hS (fun i => (zarSpaces f T h₀).obj (V i))
            (fun i => (zarSpaces f T h₀).map (homOfLE (hV i))) i j)
          ((zarCone f T h₀).leg (V j)) _ h (s j) := by
    intro i j h
    have sq := isPullback_zarSpaces_map_inf f T h₀ (hV i) (hV j)
    have hpair := AlgebraicSpaces.isPullback_fiberProduct B S hS
      ((zarSpaces f T h₀).map (homOfLE (hV i))) ((zarSpaces f T h₀).map (homOfLE (hV j)))
    set e := sq.isoIsPullback _ _ hpair with he
    have he₁ := sq.isoIsPullback_hom_fst _ _ hpair
    have he₂ := sq.isoIsPullback_hom_snd _ _ hpair
    have ht : e.hom ≫ QuasiCoherentDescent.pairFst B S hS
        (fun i => (zarSpaces f T h₀).obj (V i))
        (fun i => (zarSpaces f T h₀).map (homOfLE (hV i))) i j ≫ (zarCone f T h₀).leg (V i) =
        (zarCone f T h₀).leg (V i ⊓ V j) := by
      rw [← Category.assoc, he₁]
      exact (zarCone f T h₀).w _
    apply (restrictForm_bijective_of_inv B S hS e.hom e.inv e.hom_inv_id e.inv_hom_id _ _ ht
      N N').1
    refine (QuasiCoherentDescent.restrictForm_comp B S hS e.hom _ _ _ rfl _ he₁ _ ht
      ((zarCone f T h₀).w _) (s i)).trans (Eq.trans ?_
        (QuasiCoherentDescent.restrictForm_comp B S hS e.hom _ _ _ h _ he₂ _ ht
          ((zarCone f T h₀).w _) (s j)).symm)
    exact (hres _ (s i)).symm.trans
      ((hs i j).trans (hres _ (s j)))
  obtain ⟨t, ht, hu⟩ := existsUnique_restrictForm_eq B S hS (M := N) (N := N')
    ((zarCone f T h₀).leg U) (fun i => (zarSpaces f T h₀).obj (V i))
    (fun i => (zarSpaces f T h₀).map (homOfLE (hV i)))
    (fun i => isEtale_zarSpaces_map f T h₀ (homOfLE (hV i)))
    (isEtaleCovering_zarSpaces_map f T h₀ V hV hsup)
    (fun i => (zarCone f T h₀).leg (V i)) (fun i => (zarCone f T h₀).w (homOfLE (hV i))) s hx
  exact ⟨t, fun i => (hres (hV i) t).trans
      (ht i),
    fun t' h' => hu t' fun i =>
      (hres (hV i) t').symm.trans (h' i)⟩

/-- **The relative Hom presheaves of modules along the Zariski cone are sheaves**: the
hypothesis `hsh` of `CategoryTheory.PullbackData.existsUnique_relHomMap_glue` at
`AlgebraicGeometry.Space.modulePullbackDataTopos` and `AlgebraicGeometry.Space.zarCone f T h₀`
holds. -/
theorem zarConeRelHomIsSheaf : ZarConeRelHomIsSheaf f T h₀ := fun N N' =>
  PullbackData.relHomOpens_isSheaf_ofEq (modulePullbackData B S hS)
    (modulePullbackData_isCoherent B S hS) _ _ (modulePullbackDataTopos_isCoherent B S hS)
    (zarCone f T h₀) N N' (modulePullbackData_relHomOpens_zarCone_isSheaf f T h₀ N N')

end AlgebraicGeometry.Space

end
