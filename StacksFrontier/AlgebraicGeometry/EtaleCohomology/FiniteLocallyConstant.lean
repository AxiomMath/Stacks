module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FiniteLocallyConstant.SliceConstantSheaf
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FiniteLocallyConstant.SplitOver
public import StacksFrontier.AlgebraicGeometry.Size.FiniteType
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.Precoverage
public import StacksFrontier.CategoryTheory.Sites.Density
public import StacksFrontier.CategoryTheory.Sites.LocallyConstant.Defs

/-!
# Finite locally constant sheaves on the small étale site

A sheaf of sets on the small étale site of a scheme which is represented by a scheme finite
étale over the base is finite locally constant: on each member of an étale covering
trivializing the representing object, the sheaf becomes the constant sheaf on the finite set
of sheets.

## Main results

* `Stacks.EtaleCohomology.isFiniteLocallyConstant_of_finiteEtaleRepresentable` — one direction
  of Stacks 59.64.4 (Tag 03RV): a sheaf isomorphic to the sheafified Yoneda sheaf of an object
  of the small étale site whose structure morphism is finite is finite locally constant.

## Implementation notes

The small étale site is `AlgebraicGeometry.SmallEtale`, presented using a chosen big étale
site; its objects are schemes below the chosen size cutoff, equipped with an étale structure
morphism. Building a covering therefore has three obligations for each member: an étale
morphism of schemes, a size bound, and joint surjectivity. Size bounds come from Stacks 04T7
(`AlgebraicGeometry.Scheme.size_le_of_locallyOfFiniteType`) for the affine members of the
trivializing covering, and from Stacks 000R (3) for the open subschemes appearing in the local
factorization of a section.

The trivialization itself is used through `Stacks.Etale.IsSplitOver`, the repackaging of
Stacks 04HN as sheet data, which is what the local injectivity and local surjectivity of the
comparison map with the constant presheaf need; and the comparison is turned into an
isomorphism of sheaves by `Stacks.ConstantSheaf.constantSheafObjIsoOverPullback`.

The converse direction — a finite locally constant sheaf is representable by a finite étale
scheme — uses effective descent for schemes affine over the base (Stacks 0245). Both directions
together are Tag 03RV, stated as
`Stacks.EtaleCohomology.isFiniteLocallyConstant_iff_finiteEtaleRepresentable`.

## References

* [Stacks Project, Tag 03RV](https://stacks.math.columbia.edu/tag/03RV)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

universe u

namespace Stacks.EtaleCohomology

variable (B : AlgebraicGeometry.BigEtaleSite.{u}) {S : Scheme.{u}} (hS : B.Contains S)

/-! ### Objects, morphisms and coverings of the small étale site -/

/-- An object of the small étale site of `S`: a scheme below the size cutoff of the chosen big
étale site, together with an étale morphism to `S`. -/
public def mkObj (Y : Scheme.{u}) (p : Y ⟶ S) (hY : B.Contains Y) (hp : Etale p) :
    SmallEtale B S hS :=
  ⟨Over.mk (ObjectProperty.homMk p : B.obj Y hY ⟶ B.obj S hS), hp⟩

/-- The underlying scheme of an object built from a scheme étale over `S` is that scheme. -/
@[simp]
public theorem toScheme_obj_mkObj (Y : Scheme.{u}) (p : Y ⟶ S) (hY : B.Contains Y)
    (hp : Etale p) : (SmallEtale.toScheme B S hS).obj (mkObj B hS Y p hY hp) = Y :=
  rfl

/-- The structure morphism of an object built from a scheme étale over `S` is the given étale
morphism. -/
@[simp]
public theorem hom_mkObj (Y : Scheme.{u}) (p : Y ⟶ S) (hY : B.Contains Y) (hp : Etale p) :
    B.inclusion.map (mkObj B hS Y p hY hp).obj.hom = p :=
  rfl

/-- The structure morphism of an object of the small étale site is étale. -/
public theorem etale_hom (V : SmallEtale B S hS) : Etale (B.inclusion.map V.obj.hom) :=
  V.property

/-- The underlying scheme of an object of the small étale site lies below the size cutoff. -/
public theorem contains_toScheme_obj (V : SmallEtale B S hS) :
    B.Contains ((SmallEtale.toScheme B S hS).obj V) :=
  V.obj.left.property

/-- A morphism of the small étale site of `S` from a morphism of the underlying schemes
commuting with the structure morphisms. -/
public def mkHom {V W : SmallEtale B S hS}
    (g : (SmallEtale.toScheme B S hS).obj V ⟶ (SmallEtale.toScheme B S hS).obj W)
    (hg : g ≫ B.inclusion.map W.obj.hom = B.inclusion.map V.obj.hom) : V ⟶ W :=
  ObjectProperty.homMk (Over.homMk (ObjectProperty.homMk g) (by
    apply ObjectProperty.hom_ext
    exact hg))

/-- The underlying morphism of schemes of a morphism built from one is that morphism. -/
@[simp]
public theorem toScheme_map_mkHom {V W : SmallEtale B S hS}
    (g : (SmallEtale.toScheme B S hS).obj V ⟶ (SmallEtale.toScheme B S hS).obj W)
    (hg : g ≫ B.inclusion.map W.obj.hom = B.inclusion.map V.obj.hom) :
    (SmallEtale.toScheme B S hS).map (mkHom B hS g hg) = g :=
  rfl

/-- A morphism of the small étale site commutes with the structure morphisms. -/
@[simp]
public theorem toScheme_map_comp_hom {V W : SmallEtale B S hS} (g : V ⟶ W) :
    (SmallEtale.toScheme B S hS).map g ≫ B.inclusion.map W.obj.hom =
      B.inclusion.map V.obj.hom :=
  congrArg B.inclusion.map (Over.w g.hom)

/-- Every morphism of the small étale site is étale on underlying schemes: it is a morphism
between schemes étale over `S`. -/
public instance etale_toScheme_map {V W : SmallEtale B S hS} (g : V ⟶ W) :
    Etale ((SmallEtale.toScheme B S hS).map g) := by
  have := etale_hom B hS W
  have : Etale ((SmallEtale.toScheme B S hS).map g ≫ B.inclusion.map W.obj.hom) := by
    rw [toScheme_map_comp_hom]
    exact etale_hom B hS V
  exact Etale.of_comp _ (B.inclusion.map W.obj.hom)

/-- A family of morphisms of the small étale site whose underlying morphisms of schemes are
jointly surjective is a covering family. -/
public theorem ofArrows_mem_precoverage {V : SmallEtale B S hS} {I : Type*}
    (Y : I → SmallEtale B S hS) (g : ∀ i, Y i ⟶ V)
    (hsurj : ∀ x : (SmallEtale.toScheme B S hS).obj V, ∃ i,
      x ∈ Set.range ((SmallEtale.toScheme B S hS).map (g i))) :
    Presieve.ofArrows Y g ∈ SmallEtale.precoverage B S hS V := by
  rw [smallEtale_precoverage_eq_comap B (B.obj S hS), Precoverage.mem_comap_iff,
    bigEtaleOver_precoverage_eq_comap B S hS, Precoverage.mem_comap_iff,
    bigEtalePrecoverage_eq_comap B, Precoverage.mem_comap_iff, Presieve.map_ofArrows,
    Presieve.map_ofArrows, Presieve.map_ofArrows]
  exact (Scheme.ofArrows_mem_precoverage_iff @Etale).mpr
    ⟨hsurj, fun i ↦ etale_toScheme_map B hS (g i)⟩

/-- The sieve generated by a jointly surjective family is a covering sieve of the small étale
topology. -/
public theorem ofArrows_mem_topology {V : SmallEtale B S hS} {I : Type*}
    (Y : I → SmallEtale B S hS) (g : ∀ i, Y i ⟶ V)
    (hsurj : ∀ x : (SmallEtale.toScheme B S hS).obj V, ∃ i,
      x ∈ Set.range ((SmallEtale.toScheme B S hS).map (g i))) :
    Sieve.ofArrows Y g ∈ SmallEtale.topology B S hS V :=
  Precoverage.generate_mem_toGrothendieck (ofArrows_mem_precoverage B hS Y g hsurj)

/-- An object of the small étale site with empty underlying scheme is covered by the empty
family, so every sieve on it is a covering sieve. -/
public theorem bot_mem_topology {V : SmallEtale B S hS}
    (hV : IsEmpty ((SmallEtale.toScheme B S hS).obj V)) :
    (⊥ : Sieve V) ∈ SmallEtale.topology B S hS V := by
  have hbot : Sieve.ofArrows (fun _ : PEmpty.{1} ↦ V) (fun i ↦ PEmpty.elim i) =
      (⊥ : Sieve V) := by
    simp [Sieve.ofArrows, Presieve.ofArrows_of_isEmpty]
  rw [← hbot]
  exact ofArrows_mem_topology B hS _ _ fun x ↦ hV.elim x

/-- Two morphisms of the small étale site with the same underlying morphism of schemes are
equal. -/
public theorem hom_ext {V W : SmallEtale B S hS} {a b : V ⟶ W}
    (hab : (SmallEtale.toScheme B S hS).map a = (SmallEtale.toScheme B S hS).map b) : a = b :=
  (SmallEtale.toScheme B S hS).map_injective hab

/-! ### The trivializing covering -/

section Cover

variable (V : SmallEtale B S hS) {W : Scheme.{u}}
  (p : W ⟶ (SmallEtale.toScheme B S hS).obj V) (hp : Etale p) (a : W.affineOpens)

/-- An affine member of a covering of `V`: an affine open of a scheme étale over `V` is affine
and of finite type over `V`, hence lies below the size cutoff by Stacks 04T7, and it is étale
over `S`. -/
public def coverObj : SmallEtale B S hS :=
  have := hp
  have : IsAffine (a.1 : Scheme.{u}) := a.2
  have := etale_hom B hS V
  mkObj B hS (a.1 : Scheme.{u}) (a.1.ι ≫ p ≫ B.inclusion.map V.obj.hom)
    ((Scheme.size_le_of_locallyOfFiniteType (a.1.ι ≫ p)).trans_lt
      (contains_toScheme_obj B hS V)) inferInstance

/-- The structure morphism of an affine member of a covering of `V`. -/
public def coverHom : coverObj B hS V p hp a ⟶ V :=
  mkHom B hS (a.1.ι ≫ p) (Category.assoc _ _ _)

/-- The underlying morphism of schemes of the structure morphism of an affine member. -/
@[simp]
public theorem toScheme_map_coverHom :
    (SmallEtale.toScheme B S hS).map (coverHom B hS V p hp a) = a.1.ι ≫ p :=
  rfl

/-- A member of a covering of `V` by open subschemes: an open subscheme of a scheme étale over
`S` is étale over `S` and lies below the size cutoff by Stacks 000R (3). -/
public def openObj {Y : Scheme.{u}} (r : Y ⟶ (SmallEtale.toScheme B S hS).obj V)
    (hr : IsOpenImmersion r) : SmallEtale B S hS :=
  have := hr
  have := etale_hom B hS V
  mkObj B hS Y (r ≫ B.inclusion.map V.obj.hom)
    (Scheme.size_lt_of_isOpenImmersion r (contains_toScheme_obj B hS V)) inferInstance

/-- The structure morphism of a member of a covering of `V` by open subschemes. -/
public def openHom {Y : Scheme.{u}} (r : Y ⟶ (SmallEtale.toScheme B S hS).obj V)
    (hr : IsOpenImmersion r) : openObj B hS V r hr ⟶ V :=
  mkHom B hS r rfl

/-- The underlying morphism of schemes of the structure morphism of an open member. -/
@[simp]
public theorem toScheme_map_openHom {Y : Scheme.{u}}
    (r : Y ⟶ (SmallEtale.toScheme B S hS).obj V)
    (hr : IsOpenImmersion r) :
    (SmallEtale.toScheme B S hS).map (openHom B hS V r hr) = r :=
  rfl

end Cover

/-- **The trivializing covering.** Let `U` be an object of the small étale site of `S` whose
structure morphism is finite, hence finite étale, and let `V` be any object. There is a
covering of `V` on each member of which `U` has sheet data: Stacks 04HN gives an étale
neighbourhood of each point of `V` over which `U` becomes a finite disjoint union of copies of
the base, and each neighbourhood is refined by its affine opens, which are objects of the
site. -/
public theorem exists_cover_isSplitOver (U V : SmallEtale B S hS)
    (hU : IsFinite (B.inclusion.map U.obj.hom)) :
    ∃ (I : Type (u + 1)) (Y : I → SmallEtale B S hS) (g : ∀ i, Y i ⟶ V),
      Sieve.ofArrows Y g ∈ SmallEtale.topology B S hS V ∧
        ∀ i, Nonempty (Stacks.Etale.IsSplitOver (B.inclusion.map U.obj.hom)
          (B.inclusion.map (Y i).obj.hom)) := by
  have hUe : Etale (B.inclusion.map U.obj.hom) := etale_hom B hS U
  choose W g hg w hw hsplit using fun v : (SmallEtale.toScheme B S hS).obj V ↦
    Stacks.Etale.exists_isSplitOver (B.inclusion.map U.obj.hom) (B.inclusion.map V.obj.hom) v
  refine ⟨ULift.{u + 1} (Σ v : (SmallEtale.toScheme B S hS).obj V, (W v).affineOpens),
    fun i ↦ coverObj B hS V (g i.down.1) (hg i.down.1) i.down.2,
    fun i ↦ coverHom B hS V (g i.down.1) (hg i.down.1) i.down.2, ?_, ?_⟩
  · refine ofArrows_mem_topology B hS _ _ fun x ↦ ?_
    obtain ⟨b, hb, hwb, -⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.mp
      (W x).isBasis_affineOpens (U := ⊤) (x := w x) trivial
    exact ⟨ULift.up ⟨x, ⟨b, hb⟩⟩, ⟨w x, hwb⟩, hw x⟩
  · exact fun i ↦ (hsplit i.down.1).map fun h ↦ h.comp i.down.2.1.ι

/-! ### Local constancy on a member of the trivializing covering -/

section Constancy

variable (U V : SmallEtale B S hS)
  (h : Stacks.Etale.IsSplitOver (B.inclusion.map U.obj.hom) (B.inclusion.map V.obj.hom))

/-- The morphism of the small étale site to `U` given by a sheet of sheet data over `V`. -/
public def sheetHom (i : h.I) : V ⟶ U :=
  mkHom B hS (h.sheet i) (h.sheet_comp i)

/-- The underlying morphism of schemes of the morphism given by a sheet is that sheet. -/
@[simp]
public theorem toScheme_map_sheetHom (i : h.I) :
    (SmallEtale.toScheme B S hS).map (sheetHom B hS U V h i) = h.sheet i :=
  rfl

/-- **The comparison map.** On the localized site at `V`, the sheets of sheet data for `U` over
`V` define a map from the constant presheaf on the finite index set of sheets to the
restriction of the presheaf represented by `U`: an object of the localized site is sent to the
composite of its structure morphism with the chosen sheet. -/
public def constToYoneda :
    (Functor.const (Over V)ᵒᵖ).obj (ULift.{u + 1} h.I) ⟶
      (Over.forget V).op ⋙ uliftYoneda.{u + 1}.obj U where
  app Z := TypeCat.ofHom (fun i ↦ ULift.up (Z.unop.hom ≫ sheetHom B hS U V h i.down))
  naturality Z Z' f := by
    ext i
    refine ULift.ext _ _ ?_
    change Z'.unop.hom ≫ sheetHom B hS U V h i.down =
      f.unop.left ≫ Z.unop.hom ≫ sheetHom B hS U V h i.down
    rw [← Category.assoc, Over.w f.unop]

/-- The comparison map sends the index of a sheet to the structure morphism followed by that
sheet. -/
@[simp]
public theorem constToYoneda_app (Z : (Over V)ᵒᵖ) (i : ULift.{u + 1} h.I) :
    ConcreteCategory.hom ((constToYoneda B hS U V h).app Z) i =
      ULift.up (Z.unop.hom ≫ sheetHom B hS U V h i.down) :=
  rfl

/-- The comparison map is locally injective: two distinct sheets agree only over an empty
scheme, and an object of the small étale site with empty underlying scheme is covered by the
empty family. -/
public theorem isLocallyInjective_constToYoneda :
    Presheaf.IsLocallyInjective ((SmallEtale.topology B S hS).over V)
      (constToYoneda B hS U V h) where
  equalizerSieve_mem {Z} x y hxy := by
    by_cases hij : x.down = y.down
    · rw [show x = y from ULift.ext _ _ hij, Presheaf.equalizerSieve_self_eq_top]
      exact ((SmallEtale.topology B S hS).over V).top_mem _
    · have h1 : Z.unop.hom ≫ sheetHom B hS U V h x.down =
          Z.unop.hom ≫ sheetHom B hS U V h y.down := congrArg ULift.down hxy
      have h2 : (SmallEtale.toScheme B S hS).map Z.unop.hom ≫ h.sheet x.down =
          (SmallEtale.toScheme B S hS).map Z.unop.hom ≫ h.sheet y.down := by
        simpa only [Functor.map_comp, toScheme_map_sheetHom] using
          congrArg (SmallEtale.toScheme B S hS).map h1
      rw [GrothendieckTopology.mem_over_iff]
      exact (SmallEtale.topology B S hS).superset_covering bot_le
        (bot_mem_topology B hS (h.isEmpty_of_sheet_eq _ hij h2))

/-- The comparison map is locally surjective: a `V`-point of `U` agrees with a sheet on each
member of an open covering of its source, and those members are objects of the small étale
site. -/
public theorem isLocallySurjective_constToYoneda :
    Presheaf.IsLocallySurjective ((SmallEtale.topology B S hS).over V)
      (constToYoneda B hS U V h) where
  imageSieve_mem {Z} s := by
    obtain ⟨κ, Y, q, hq, idx, hcov, hfac⟩ := h.exists_openCover
      ((SmallEtale.toScheme B S hS).map Z.hom) ((SmallEtale.toScheme B S hS).map s.down)
      (by rw [toScheme_map_comp_hom, toScheme_map_comp_hom])
    rw [GrothendieckTopology.mem_over_iff]
    refine (SmallEtale.topology B S hS).superset_covering ?_
      (ofArrows_mem_topology B hS (fun k ↦ openObj B hS Z.left (q k) (hq k))
        (fun k ↦ openHom B hS Z.left (q k) (hq k)) fun x ↦ (hcov x).imp fun k hk ↦ hk)
    rw [Sieve.ofArrows, Sieve.generate_le_iff]
    rintro T f ⟨k⟩
    rw [Sieve.overEquiv_iff]
    have key : (openHom B hS Z.left (q k) (hq k) ≫ Z.hom) ≫ sheetHom B hS U V h (idx k) =
        openHom B hS Z.left (q k) (hq k) ≫ s.down := by
      refine hom_ext B hS ?_
      simp only [Functor.map_comp, toScheme_map_openHom, toScheme_map_sheetHom, Category.assoc]
      exact (hfac k).symm
    exact ⟨ULift.up (idx k), ULift.ext _ _ key⟩

/-- **The local constancy.** On an object of the small étale site over which `U` has sheet
data, the restriction of the sheaf represented by `U` is the constant sheaf on the finite set
of sheets. -/
public theorem isConstant_overPullback_sheafifiedYoneda :
    Nonempty ((constantSheaf ((SmallEtale.topology B S hS).over V) (Type (u + 1))).obj
        (ULift.{u + 1} h.I) ≅
      ((SmallEtale.topology B S hS).overPullback (Type (u + 1)) V).obj
        ((Sheaf.sheafifiedYoneda (SmallEtale.topology B S hS)).obj U)) :=
  ⟨Stacks.ConstantSheaf.constantSheafObjIsoOverPullback _ V (constToYoneda B hS U V h)
    (isLocallyInjective_constToYoneda B hS U V h)
    (isLocallySurjective_constToYoneda B hS U V h)⟩

end Constancy

/-! ### The theorem -/

/-- **Stacks 03RV, the direction that does not need descent.** A sheaf of sets on the small
étale site of `X` which is represented by an object of the site whose structure morphism is
finite — that is, by a scheme finite étale over `X` — is finite locally constant: the
trivializing covering of Stacks 04HN makes it constant with value the finite set of sheets on
each member.

The equivalence of Tag 03RV, which adds the converse, is
`Stacks.EtaleCohomology.isFiniteLocallyConstant_iff_finiteEtaleRepresentable`. -/
public theorem isFiniteLocallyConstant_of_finiteEtaleRepresentable
    (B : AlgebraicGeometry.BigEtaleSite.{u}) (X : B.Scheme)
    (F : Sheaf (SmallEtale.topology B X.1 X.property) (Type (u + 1)))
    (hF : ∃ U : SmallEtale B X.1 X.property,
      IsFinite (B.inclusion.map U.obj.hom) ∧
        Nonempty (F ≅
          (Sheaf.sheafifiedYoneda (SmallEtale.topology B X.1 X.property)).obj U)) :
    Stacks.ConstantSheaf.IsFiniteLocallyConstant
      (SmallEtale.topology B X.1 X.property) F := by
  obtain ⟨U, hU, ⟨e⟩⟩ := hF
  refine ⟨fun V ↦ ?_⟩
  obtain ⟨I, Y, g, hcov, hsplit⟩ := exists_cover_isSplitOver B X.property U V hU
  refine ⟨I, Y, g, hcov, fun i ↦ ?_⟩
  obtain ⟨h⟩ := hsplit i
  have hfin : Finite h.I := h.finite_I
  refine ⟨ULift.{u + 1} h.I, inferInstance, ?_⟩
  obtain ⟨c⟩ := isConstant_overPullback_sheafifiedYoneda B X.property U (Y i) h
  exact ⟨c ≪≫ (((SmallEtale.topology B X.1 X.property).overPullback
    (Type (u + 1)) (Y i)).mapIso e).symm⟩

end Stacks.EtaleCohomology
