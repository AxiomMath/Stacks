module

public import StacksFrontier.AlgebraicGeometry.Descent.FamilyEffectivityLargeIndex
public import StacksFrontier.AlgebraicGeometry.Descent.FpqcEffective023T
public import StacksFrontier.AlgebraicGeometry.Descent.PullbackSectionsSheaf.HomPresheaf
public import StacksFrontier.AlgebraicGeometry.ModuleLimits.CanonicalRestriction
public import StacksFrontier.AlgebraicGeometry.PicardScheme.PicardSequenceSplitExact
public import StacksFrontier.AlgebraicGeometry.Quot.PolarizedLimitDescentHom
public import StacksFrontier.AlgebraicGeometry.Quot.PolarizedStackUnconditional
public import StacksFrontier.AlgebraicGeometry.Stacks.RepresentableDiagonal
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf.FibreProducts
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf.SieveToFamily

/-!
# The isomorphism presheaves of `𝒫olarized` are fppf sheaves

Let `x` and `y` be two polarized families over an object `U` of the big fppf site of a terminal
base scheme, read as objects of the fibre of the stack `𝒫olarized` of Stacks 0D1M over `U`. The
presheaf `Isom(x, y)` of Stacks 02ZB, transported to the big fppf site of `U` along the iterated
slice equivalence, is a sheaf for the fppf topology. This is the sheaf property that the proof of
Stacks 0D42 needs before it can glue local representations of `Isom(x, y)` by Stacks 01JJ.

## Main definitions

* `AlgebraicGeometry.polarizedIsomPresheaf`: the presheaf `Isom(x, y)` on the big fppf site of
  `U`.
* `AlgebraicGeometry.polarizedRestriction`, `AlgebraicGeometry.polarizedRestrictionMap` and
  `AlgebraicGeometry.polarizedMorPresheaf`: the chosen pullbacks of a polarized family to the
  objects of the big fppf site of `U`, their restriction maps, and the presheaf `Mor(x, y)` on
  that site.
* `AlgebraicGeometry.polarizedIsomPresheafObjEquiv`: a section of `Isom(x, y)` over `V` is a
  morphism of the fibre over `V` between the chosen pullbacks of `x` and `y`, and
  `AlgebraicGeometry.polarizedFiberHomEquiv`: such a morphism is a morphism of polarized families
  whose base map is the identity of `V`, read through the identifications of the two bases
  with `V`.
* `AlgebraicGeometry.PolarizedFamily.lineBundleComparison`: the morphism of pulled-back
  polarizations that a morphism of polarized families must restrict to on a member of a
  covering family.

## Main results

* `AlgebraicGeometry.isSheaf_polarizedIsomPresheaf`: **`Isom(x, y)` is an fppf sheaf.**
* `AlgebraicGeometry.isSheafFor_polarizedMorPresheaf`: `Mor(x, y)` satisfies the sheaf condition
  for every family of the big fppf site of `U` whose underlying morphisms of schemes form an fppf
  covering.
* `AlgebraicGeometry.polarizedIsomPresheaf_map_eq_iff`: the restriction maps of `Isom(x, y)` in
  terms of the restriction maps of the chosen pullbacks.
* `AlgebraicGeometry.BigFppfOver.isSheaf_of_isSheafFor_isCovering`: a presheaf on the big fppf
  site of a scheme is a sheaf as soon as it satisfies the sheaf condition for the chosen covering
  families.
* `AlgebraicGeometry.PolarizedFamily.Hom.ext_of_comp_eq_of_mem_fpqcPrecoverage` and
  `AlgebraicGeometry.PolarizedFamily.Hom.exists_comp_eq_of_mem_fpqcPrecoverage`: morphisms of
  polarized families are determined by, and glue from, their composites with a family of
  morphisms whose maps of total spaces form an fpqc covering.

## Implementation notes

The fibre of `𝒫olarized` over `V` is a groupoid, so `Isom(x, y)` is the presheaf `Mor(x, y)`
(`AlgebraicGeometry.Stack.isomPresheafIsoMorPresheaf`), and the work is the sheaf condition for
`Mor(x, y)` along a chosen fppf covering family `{Vᵢ ⟶ V}`. Write `x_V` and `x_{Vᵢ}` for the chosen
pullbacks. Because the squares of total spaces of `x_{Vᵢ} ⟶ x_V` are cartesian, the maps of total
spaces `X_{Vᵢ} ⟶ X_V` form an fppf, hence fpqc, covering of the scheme `X_V`; the total spaces
themselves need not lie in the site.

* *Total maps.* A compatible family of sections `mᵢ : x_{Vᵢ} ⟶ y_{Vᵢ}` gives maps
  `X_{Vᵢ} ⟶ Y_{Vᵢ} ⟶ Y_V`, which glue to `M : X_V ⟶ Y_V` because fpqc coverings of schemes are
  effective epimorphic (Mathlib's subcanonicity of the fpqc topology). The compatibility needed
  there concerns an arbitrary scheme `Z` mapping to two members; it is reduced to the
  compatibility of the family over the fibre product `Vᵢ ×_V Vⱼ`, which lies in the site, by
  lifting `Z` to the total space of the chosen pullback over that fibre product
  (`AlgebraicGeometry.exists_lift_polarizedRestriction`).
* *Cartesian square.* A morphism of the fibre has identity base map, so its square is cartesian
  exactly when its map of total spaces is an isomorphism. The inverses `mᵢ⁻¹` form a compatible
  family of `Mor(y, x)`, whose glued map is inverse to `M`.
* *Polarizations.* The comparisons of polarizations glue by fpqc descent of morphisms of
  quasi-coherent modules (`Stacks.Picard.exists_map_eq_of_pullHom_eq` with
  `Stacks.Picard.bijective_toDescentData_map_of_fpqc`), stated through
  `Stacks.AlgebraicGeometry.ModuleLimits.canStep`, whose composition law and whose compatibility
  with composition of polarized families (`PolarizedFamily.canStep_lineBundleComparison`) reduce
  the compatibility on `Z` to the one over the fibre product again; the inverses glue too, so the
  glued comparison is an isomorphism.

The structure functor `(polarizedStackUnconditional B hS hT).val.p` is only definitionally equal
to `AlgebraicGeometry.polarizedSliceProjection` after unfolding the semireducible
`InducedBicategory`, which makes the former unusable for rewriting; all lemmas are therefore
stated for `polarizedSliceProjection`, and the two instances of `Functor.IsFibered` declared here
(`AlgebraicGeometry.isFibered_polarizedSliceProjection` and
`AlgebraicGeometry.instIsFiberedPolarizedStackUnconditional`) make both spellings fibred.
Without the second one the presheaf `Isom(x, y)` of `polarizedStackUnconditional` cannot even be
formed.

## References

* [Stacks Project, Tag 0D42](https://stacks.math.columbia.edu/tag/0D42)
* [Stacks Project, Tag 02ZB](https://stacks.math.columbia.edu/tag/02ZB)
* [Stacks Project, Tag 023Q](https://stacks.math.columbia.edu/tag/023Q)
* [Stacks Project, Tag 023T](https://stacks.math.columbia.edu/tag/023T)
* [Stacks Project, Tag 0D1M](https://stacks.math.columbia.edu/tag/0D1M)
-/

@[expose] public noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.AlgebraicGeometry.ModuleLimits (canHom canIso canStep canHom_comp canHom_comp_assoc
  canIso_hom canStep_canStep eq_canStep_of_canHom_comp)

namespace Stacks.AlgebraicGeometry.ModuleLimits

open _root_.AlgebraicGeometry

/-- Carrying an isomorphism between pullbacks along a further pullback gives an isomorphism. -/
instance isIso_canStep {Zk Zj Zi : Scheme.{u}} (m : Zk ⟶ Zj) (g : Zj ⟶ Zi) (mg : Zk ⟶ Zi)
    (hmg : m ≫ g = mg) {F G : Zi.Modules}
    (ψ : (Scheme.Modules.pullback g).obj F ⟶ (Scheme.Modules.pullback g).obj G) [IsIso ψ] :
    IsIso (canStep m g mg hmg ψ) := by
  rw [canStep]; infer_instance

/-- Carrying a morphism between pullbacks along a further pullback commutes with inversion. -/
theorem canStep_inv {Zk Zj Zi : Scheme.{u}} (m : Zk ⟶ Zj) (g : Zj ⟶ Zi) (mg : Zk ⟶ Zi)
    (hmg : m ≫ g = mg) {F G : Zi.Modules}
    (ψ : (Scheme.Modules.pullback g).obj F ⟶ (Scheme.Modules.pullback g).obj G) [IsIso ψ] :
    canStep m g mg hmg (inv ψ) = inv (canStep m g mg hmg ψ) := by
  refine IsIso.eq_inv_of_hom_inv_id ?_
  rw [canStep, canStep]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  rw [← Functor.map_comp_assoc, IsIso.hom_inv_id, CategoryTheory.Functor.map_id,
    Category.id_comp, Iso.inv_hom_id]

end Stacks.AlgebraicGeometry.ModuleLimits

namespace CategoryTheory

/-- Conjugating the members of a covering presieve by identifications of the sources and of the
target given by equalities of objects keeps it covering. -/
theorem Presieve.ofArrows_eqToHom_mem {C : Type*} [Category C] (J : Precoverage C) {X X' : C}
    (hX : X = X') {ι : Type*} {Y Y' : ι → C} (hY : ∀ i, Y' i = Y i) {f : ∀ i, Y i ⟶ X}
    (h : Presieve.ofArrows Y f ∈ J X) :
    Presieve.ofArrows Y' (fun i => eqToHom (hY i) ≫ f i ≫ eqToHom hX) ∈ J X' := by
  subst hX
  obtain rfl : Y' = Y := funext hY
  simpa using h

/-- Conjugating the four sides of a pullback square by identifications of its vertices given by
equalities of objects keeps it a pullback square. -/
theorem IsPullback.eqToHom_conj {C : Type*} [Category C] {P X Y Z P' X' Y' Z' : C}
    {fst : P ⟶ X} {snd : P ⟶ Y} {f : X ⟶ Z} {g : Y ⟶ Z} (h : IsPullback fst snd f g)
    (eP : P' = P) (eX : X = X') (eY : Y = Y') (eZ : Z = Z') :
    IsPullback (eqToHom eP ≫ fst ≫ eqToHom eX) (eqToHom eP ≫ snd ≫ eqToHom eY)
      (eqToHom eX.symm ≫ f ≫ eqToHom eZ) (eqToHom eY.symm ≫ g ≫ eqToHom eZ) := by
  subst eP eX eY eZ
  simpa using h

/-- A composite of a morphism with identifications given by equalities of objects equals the
same morphism conjugated by any other such identifications with the same endpoints. -/
theorem eqToHom_comp_comp_eqToHom_eq {C : Type*} [Category C] {P X Q Y Px Py : C}
    (a₁ : P = X) (g : X ⟶ Y) (a₂ : Y = Px) (a₃ : Px = Py) (b₁ : P = X) (b₂ : X = Q)
    (c₁ : Q = X) (c₂ : Y = Py) :
    (eqToHom a₁ ≫ g ≫ eqToHom a₂) ≫ eqToHom a₃ =
      (eqToHom b₁ ≫ 𝟙 X ≫ eqToHom b₂) ≫ (eqToHom c₁ ≫ g ≫ eqToHom c₂) := by
  subst a₁ a₂ a₃ b₂
  simp

end CategoryTheory

namespace AlgebraicGeometry

/-! ### The sheaf condition on the big fppf site of a scheme -/

section SiteReduction

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The sieve generated by a chosen covering family of the big fppf site of `S` is a covering
sieve. -/
theorem BigFppfOver.sieve₀_mem_topology_of_isCovering {X : BigFppfOver B S hS}
    {E : PreZeroHypercover.{u + 1} X} (hE : BigFppfOver.IsCovering B S hS ⟨X, E⟩) :
    E.sieve₀ ∈ BigFppfOver.topology B S hS X := by
  rw [GrothendieckTopology.mem_over_iff, PreZeroHypercover.sieve₀, Sieve.overEquiv_ofArrows]
  exact Precoverage.generate_mem_toGrothendieck
    ⟨E.map (BigFppfOver.forget B S hS), rfl, hE⟩

/-- **A presheaf on the big fppf site of `S` is a sheaf as soon as it satisfies the sheaf
condition for the chosen covering families.** Every covering sieve contains a chosen covering
family, and so does the pullback of that family's sieve along any morphism into its target; the
sheaf condition for the sieve then follows from the one for the family by
`CategoryTheory.Presieve.isSheafFor_of_factorsThru`. -/
theorem BigFppfOver.isSheaf_of_isSheafFor_isCovering {P : (BigFppfOver B S hS)ᵒᵖ ⥤ Type*}
    (h : ∀ (X : BigFppfOver B S hS) (E : PreZeroHypercover.{u + 1} X),
      BigFppfOver.IsCovering B S hS ⟨X, E⟩ → Presieve.IsSheafFor P E.presieve₀) :
    Presheaf.IsSheaf (BigFppfOver.topology B S hS) P := by
  rw [isSheaf_iff_isSheaf_of_type]
  intro X R hR
  obtain ⟨E, hE, hle⟩ := BigFppfOver.exists_isCovering_sieve₀_le B S hS hR
  refine Presieve.isSheafFor_of_factorsThru P (S := E.presieve₀) ?_ (h X E hE) ?_
  · intro Z g hg
    exact ⟨Z, 𝟙 Z, g, hle _ (Sieve.le_generate E.presieve₀ Z g hg), Category.id_comp g⟩
  · intro Y f _
    have hpb : E.sieve₀.pullback f ∈ BigFppfOver.topology B S hS Y :=
      (BigFppfOver.topology B S hS).pullback_stable f
        (BigFppfOver.sieve₀_mem_topology_of_isCovering B S hS hE)
    obtain ⟨E', hE', hle'⟩ := BigFppfOver.exists_isCovering_sieve₀_le B S hS hpb
    refine ⟨E'.presieve₀, (h Y E' hE').isSeparatedFor, ?_⟩
    intro Z g hg
    exact hle' _ (Sieve.le_generate E'.presieve₀ Z g hg)

end SiteReduction

/-! ### Gluing along fpqc coverings of schemes -/

section SchemeGluing

/-- **Morphisms of schemes glue along an fpqc covering** (Stacks 023Q): a family of morphisms
out of the members of an fpqc covering family which agree on every scheme mapping compatibly to
two members is the family of restrictions of a unique morphism out of the target. -/
theorem Scheme.existsUnique_comp_eq_of_mem_fpqcPrecoverage {ι : Type*} {X Y : Scheme.{u}}
    {Xi : ι → Scheme.{u}} (c : ∀ i, Xi i ⟶ X)
    (hc : Presieve.ofArrows Xi c ∈ Scheme.fpqcPrecoverage.{u} X) (φ : ∀ i, Xi i ⟶ Y)
    (hφ : ∀ i j (Z : Scheme.{u}) (gi : Z ⟶ Xi i) (gj : Z ⟶ Xi j),
      gi ≫ c i = gj ≫ c j → gi ≫ φ i = gj ≫ φ j) :
    ∃! M : X ⟶ Y, ∀ i, c i ≫ M = φ i := by
  have hsheaf : Presieve.IsSheaf Scheme.fpqcTopology (yoneda.obj Y) :=
    GrothendieckTopology.Subcanonical.isSheaf_of_isRepresentable _
  have h := hsheaf.isSheafFor _ (Precoverage.generate_mem_toGrothendieck hc)
  rw [Presieve.isSheafFor_arrows_iff] at h
  exact h φ hφ

/-- The pullback map on morphisms of the pullback pseudofunctor of sheaves of modules is
`Stacks.AlgebraicGeometry.ModuleLimits.canStep`. -/
theorem modulePullbackPseudofunctor_pullHom_eq_canStep {X Y Z : Scheme.{u}} (f : X ⟶ Y)
    (g : Y ⟶ Z) (h : X ⟶ Z) (w : f ≫ g = h) (M N : Z.Modules)
    (φ : (Scheme.Modules.pullback g).obj M ⟶ (Scheme.Modules.pullback g).obj N) :
    Pseudofunctor.LocallyDiscreteOpToCat.pullHom
        (F := modulePullbackPseudofunctor) φ f h h w w = canStep f g h w φ := by
  rw [modulePullbackPseudofunctor_pullHom]
  rfl

/-- **Morphisms of quasi-coherent modules glue along an fpqc covering** (Stacks 023T): a family
of morphisms between the pullbacks of two quasi-coherent modules to the members of an fpqc
covering family, whose further pullbacks agree on every scheme mapping compatibly to two
members, is the family of pullbacks of one morphism. -/
theorem Scheme.Modules.exists_map_eq_of_canStep_eq {ι : Type*} {X : Scheme.{u}}
    {Xi : ι → Scheme.{u}} (c : ∀ i, Xi i ⟶ X)
    (hc : Presieve.ofArrows Xi c ∈ Scheme.fpqcPrecoverage.{u} X) {A A' : X.Modules}
    (hA : A.IsQuasicoherent) (hA' : A'.IsQuasicoherent)
    (ψ : ∀ i, (Scheme.Modules.pullback (c i)).obj A ⟶ (Scheme.Modules.pullback (c i)).obj A')
    (h : ∀ ⦃Z : Scheme.{u}⦄ (k : Z ⟶ X) ⦃i j : ι⦄ (gi : Z ⟶ Xi i) (gj : Z ⟶ Xi j)
      (hi : gi ≫ c i = k) (hj : gj ≫ c j = k),
      canStep gi (c i) k hi (ψ i) = canStep gj (c j) k hj (ψ j)) :
    ∃ φ : A ⟶ A', ∀ i, (Scheme.Modules.pullback (c i)).map φ = ψ i := by
  exact Stacks.Picard.exists_map_eq_of_pullHom_eq c
    (Stacks.Picard.bijective_toDescentData_map_of_fpqc c hc A A' hA hA') ψ
    (fun Z k i j gi gj hi hj => by
      rw [modulePullbackPseudofunctor_pullHom_eq_canStep,
        modulePullbackPseudofunctor_pullHom_eq_canStep]
      exact h k gi gj hi hj)

end SchemeGluing

/-! ### Morphisms of polarized families along a covering of total spaces -/

namespace PolarizedFamily

variable {B : BigFppfSite.{u}}

/-- The polarization of a polarized family is quasi-coherent, being invertible. -/
theorem isQuasicoherent_lineBundle (x : PolarizedFamily B) : x.lineBundle.IsQuasicoherent :=
  Stacks.Picard.isQuasicoherent_of_isInvertible x.lineBundle
    ((Stacks.InvertiblePullback.stacksIsInvertible_iff_algebraicGeometryIsInvertible _ _ _).mpr
      x.invertible)

/-- If the base maps of a family of morphisms into a polarized family form an fppf covering, so
do their maps of total spaces: the squares are cartesian, and flatness, local finite
presentation and surjectivity are stable under base change. -/
theorem ofArrows_totalMap_mem_fppfPrecoverage {ι : Type*} {a : PolarizedFamily B}
    {a' : ι → PolarizedFamily B} (c : ∀ i, a' i ⟶ a)
    (hc : Presieve.ofArrows (fun i => B.inclusion.obj (a' i).base)
      (fun i => B.inclusion.map (c i).baseMap) ∈
        Scheme.fppfPrecoverage.{u} (B.inclusion.obj a.base)) :
    Presieve.ofArrows (fun i => (a' i).total) (fun i => (c i).totalMap) ∈
      Scheme.fppfPrecoverage.{u} a.total := by
  rw [Scheme.fppfPrecoverage, Scheme.ofArrows_mem_precoverage_iff] at hc ⊢
  obtain ⟨hsurj, hprop⟩ := hc
  refine ⟨fun z => ?_, fun i => ⟨MorphismProperty.of_isPullback (c i).cartesian.flip (hprop i).1,
    MorphismProperty.of_isPullback (c i).cartesian.flip (hprop i).2⟩⟩
  obtain ⟨i, s, hs⟩ := hsurj (a.toBase z)
  obtain ⟨w, hw, -⟩ := Scheme.Pullback.exists_preimage_pullback
    (f := a.toBase) (g := B.inclusion.map (c i).baseMap) z s hs.symm
  refine ⟨i, (c i).cartesian.isoPullback.inv w, ?_⟩
  rwa [← Scheme.Hom.comp_apply, (c i).cartesian.isoPullback_inv_fst]

/-- **Morphisms of polarized families are determined by their composites with a covering.** Two
morphisms with the same base map agree as soon as their composites with a family of morphisms
whose maps of total spaces form an fpqc covering agree: the maps of total spaces agree because
fpqc coverings are epimorphic, and the comparisons of polarizations by fpqc descent of morphisms
of quasi-coherent modules. -/
theorem Hom.ext_of_comp_eq_of_mem_fpqcPrecoverage {ι : Type*} {a b : PolarizedFamily B}
    {a' : ι → PolarizedFamily B} (c : ∀ i, a' i ⟶ a)
    (hc : Presieve.ofArrows (fun i => (a' i).total) (fun i => (c i).totalMap) ∈
      Scheme.fpqcPrecoverage.{u} a.total)
    {φ ψ : a ⟶ b} (hbase : φ.baseMap = ψ.baseMap) (h : ∀ i, c i ≫ φ = c i ≫ ψ) : φ = ψ := by
  have htot : φ.totalMap = ψ.totalMap :=
    hom_ext_of_mem_fpqcPrecoverage _ hc fun i => by
      simpa only [comp_totalMap] using congrArg Hom.totalMap (h i)
  obtain ⟨φb, φt, φc, φl⟩ := φ
  obtain ⟨ψb, ψt, ψc, ψl⟩ := ψ
  change φb = ψb at hbase
  change φt = ψt at htot
  subst hbase htot
  have hqc1 := Stacks.Modules.isQuasicoherent_pullback φt b.lineBundle
    b.isQuasicoherent_lineBundle
  have hqc2 := a.isQuasicoherent_lineBundle
  have key : φl.hom = ψl.hom :=
    Stacks.Descent.hom_ext_of_pullback_map_eq_fpqc (fun i => (c i).totalMap) hc fun i => by
      have e1 := Hom.lineBundleIso_hom_comp_of_comp_eq (c i) ⟨φb, φt, φc, φl⟩
        (c i ≫ ⟨φb, φt, φc, φl⟩) (comp_totalMap _ _).symm rfl
      have e2 := Hom.lineBundleIso_hom_comp_of_comp_eq (c i) ⟨φb, φt, ψc, ψl⟩
        (c i ≫ ⟨φb, φt, φc, φl⟩) (comp_totalMap _ _).symm (h i).symm
      exact (cancel_mono (c i).lineBundleIso.hom).1 (e1.trans e2.symm)
  exact Hom.ext rfl rfl (heq_of_eq (Iso.ext key))

/-- The comparison of polarizations which a morphism `a ⟶ b` with map of total spaces `M` must
restrict to along `c : a' ⟶ a` for its composite with `c` to be `φ : a' ⟶ b`: the canonical
identification of `c^* M^* L_b` with `φ^* L_b`, followed by the comparison of `φ` and by the
inverse of the comparison of `c`. -/
def lineBundleComparison {a a' b : PolarizedFamily B} (c : a' ⟶ a) (φ : a' ⟶ b)
    (M : a.total ⟶ b.total) (h : c.totalMap ≫ M = φ.totalMap) :
    (Scheme.Modules.pullback c.totalMap).obj ((Scheme.Modules.pullback M).obj b.lineBundle) ⟶
      (Scheme.Modules.pullback c.totalMap).obj a.lineBundle :=
  canHom c.totalMap M φ.totalMap h b.lineBundle ≫ φ.lineBundleIso.hom ≫ c.lineBundleIso.inv

/-- The comparison `AlgebraicGeometry.PolarizedFamily.lineBundleComparison` is an
isomorphism. -/
instance isIso_lineBundleComparison {a a' b : PolarizedFamily B} (c : a' ⟶ a) (φ : a' ⟶ b)
    (M : a.total ⟶ b.total) (h : c.totalMap ≫ M = φ.totalMap) :
    IsIso (lineBundleComparison c φ M h) := by
  rw [lineBundleComparison]; infer_instance

/-- **The comparison of polarizations is compatible with composition**: carrying the comparison
along `c` further along `d` gives the comparison along `d ≫ c` for the composite `d ≫ φ`. This is
the cocycle of the canonical identifications of iterated pullbacks. -/
theorem canStep_lineBundleComparison {a'' a' a b : PolarizedFamily B} (d : a'' ⟶ a')
    (c : a' ⟶ a) (φ : a' ⟶ b) (M : a.total ⟶ b.total) (h : c.totalMap ≫ M = φ.totalMap) :
    canStep d.totalMap c.totalMap (d ≫ c).totalMap (comp_totalMap d c).symm
        (lineBundleComparison c φ M h) =
      lineBundleComparison (d ≫ c) (d ≫ φ) M
        (by rw [comp_totalMap, comp_totalMap, Category.assoc, h]) := by
  symm
  refine eq_canStep_of_canHom_comp _ _ _ _ _ _ ?_
  have hφ : canHom d.totalMap φ.totalMap (d ≫ φ).totalMap (comp_totalMap d φ).symm b.lineBundle ≫
      (d ≫ φ).lineBundleIso.hom =
        (Scheme.Modules.pullback d.totalMap).map φ.lineBundleIso.hom ≫ d.lineBundleIso.hom :=
    (Hom.lineBundleIso_hom_comp_of_comp_eq d φ (d ≫ φ) (comp_totalMap d φ).symm rfl).symm
  have hc : (d ≫ c).lineBundleIso.inv = d.lineBundleIso.inv ≫
      (Scheme.Modules.pullback d.totalMap).map c.lineBundleIso.inv ≫
        canHom d.totalMap c.totalMap (d ≫ c).totalMap (comp_totalMap d c).symm a.lineBundle := by
    refine Iso.inv_ext ?_
    have e := Hom.lineBundleIso_hom_comp_of_comp_eq d c (d ≫ c) (comp_totalMap d c).symm rfl
    rw [← Iso.cancel_iso_hom_left (canIso d.totalMap c.totalMap (d ≫ c).totalMap
      (comp_totalMap d c).symm a.lineBundle), canIso_hom, ← Category.assoc, ← e,
      Category.comp_id]
    simp only [Category.assoc, Iso.hom_inv_id_assoc]
    rw [← Functor.map_comp_assoc, Iso.hom_inv_id, CategoryTheory.Functor.map_id,
      Category.id_comp]
  rw [lineBundleComparison, lineBundleComparison, hc,
    ← canHom_comp_assoc d.totalMap c.totalMap M (d ≫ c).totalMap φ.totalMap (d ≫ φ).totalMap
      (comp_totalMap d c).symm h _ (comp_totalMap d φ).symm, reassoc_of% hφ]
  simp only [CategoryTheory.Functor.map_comp, Category.assoc, Iso.hom_inv_id_assoc]

/-- **Morphisms of polarized families glue along a covering of total spaces.** Let `cᵢ : aᵢ ⟶ a`
be morphisms whose maps of total spaces form an fpqc covering and let `φᵢ : aᵢ ⟶ b`. Given a base
map `β₀` and a map of total spaces `M` forming a cartesian square, through which the base maps and
total maps of the `φᵢ` factor, and given that the comparisons of polarizations
`AlgebraicGeometry.PolarizedFamily.lineBundleComparison` agree on every scheme mapping
compatibly to two members, there is a morphism `a ⟶ b` with base map `β₀` and map of total spaces
`M` whose composites with the `cᵢ` are the `φᵢ`. -/
theorem Hom.exists_comp_eq_of_mem_fpqcPrecoverage {ι : Type*} {a b : PolarizedFamily B}
    {a' : ι → PolarizedFamily B} (c : ∀ i, a' i ⟶ a)
    (hc : Presieve.ofArrows (fun i => (a' i).total) (fun i => (c i).totalMap) ∈
      Scheme.fpqcPrecoverage.{u} a.total)
    (φ : ∀ i, a' i ⟶ b) (β₀ : a.base ⟶ b.base)
    (hbase : ∀ i, (c i).baseMap ≫ β₀ = (φ i).baseMap) (M : a.total ⟶ b.total)
    (hM : ∀ i, (c i).totalMap ≫ M = (φ i).totalMap)
    (hcart : IsPullback M a.toBase b.toBase (B.inclusion.map β₀))
    (hmod : ∀ ⦃Z : Scheme.{u}⦄ (k : Z ⟶ a.total) ⦃i j : ι⦄ (gi : Z ⟶ (a' i).total)
      (gj : Z ⟶ (a' j).total) (hi : gi ≫ (c i).totalMap = k) (hj : gj ≫ (c j).totalMap = k),
      canStep gi (c i).totalMap k hi (lineBundleComparison (c i) (φ i) M (hM i)) =
        canStep gj (c j).totalMap k hj (lineBundleComparison (c j) (φ j) M (hM j))) :
    ∃ χ : a ⟶ b, χ.baseMap = β₀ ∧ χ.totalMap = M ∧ ∀ i, c i ≫ χ = φ i := by
  have hqc1 := Stacks.Modules.isQuasicoherent_pullback M b.lineBundle
    b.isQuasicoherent_lineBundle
  have hqc2 := a.isQuasicoherent_lineBundle
  obtain ⟨α, hα⟩ := Scheme.Modules.exists_map_eq_of_canStep_eq (fun i => (c i).totalMap) hc
    hqc1 hqc2 (fun i => lineBundleComparison (c i) (φ i) M (hM i)) hmod
  obtain ⟨α', hα'⟩ := Scheme.Modules.exists_map_eq_of_canStep_eq (fun i => (c i).totalMap) hc
    hqc2 hqc1 (fun i => inv (lineBundleComparison (c i) (φ i) M (hM i)))
    (fun Z k i j gi gj hi hj => by
      rw [Stacks.AlgebraicGeometry.ModuleLimits.canStep_inv,
        Stacks.AlgebraicGeometry.ModuleLimits.canStep_inv]
      exact IsIso.inv_eq_inv.mpr (hmod k gi gj hi hj))
  let e : (Scheme.Modules.pullback M).obj b.lineBundle ≅ a.lineBundle :=
    { hom := α
      inv := α'
      hom_inv_id := Stacks.Descent.hom_ext_of_pullback_map_eq_fpqc
        (fun i => (c i).totalMap) hc fun i => by
          rw [CategoryTheory.Functor.map_comp, hα i, hα' i, IsIso.hom_inv_id,
            CategoryTheory.Functor.map_id]
      inv_hom_id := Stacks.Descent.hom_ext_of_pullback_map_eq_fpqc
        (fun i => (c i).totalMap) hc fun i => by
          rw [CategoryTheory.Functor.map_comp, hα i, hα' i, IsIso.inv_hom_id,
            CategoryTheory.Functor.map_id] }
  refine ⟨⟨β₀, M, hcart, e⟩, rfl, rfl, fun i => ?_⟩
  refine Hom.comp_eq_of_lineBundleIso_hom (c i) _ (φ i) (hbase i) (hM i) ?_
  change (Scheme.Modules.pullback (c i).totalMap).map α ≫ (c i).lineBundleIso.hom = _
  rw [hα i, lineBundleComparison]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]

end PolarizedFamily

/-! ### `𝒫olarized` over the big fppf site of `U` -/

section Polarized

variable (B : BigFppfSite.{u}) {S : Scheme.{u}} (hS : B.Contains S)
  (hT : IsTerminal (B.obj hS))

/-- `𝒫olarized`, read over the big fppf site of a terminal base scheme, is a fibred category. -/
instance isFibered_polarizedSliceProjection : (polarizedSliceProjection B hS hT).IsFibered :=
  (polarizedProjection_isFiberedInGroupoids_unconditional.sliceAtTerminal hT).isFibered

/-- The structure functor of `AlgebraicGeometry.polarizedStackUnconditional` is a fibred
category. It is `AlgebraicGeometry.polarizedSliceProjection`, but only after unfolding the
semireducible `InducedBicategory`, so instance search needs this instance to see it. -/
instance instIsFiberedPolarizedStackUnconditional :
    (polarizedStackUnconditional B hS hT).val.p.IsFibered :=
  isFibered_polarizedSliceProjection B hS hT

/-- The base of an object of the fibre of `𝒫olarized` over `W` is the underlying scheme of
`W`. -/
theorem polarizedSliceProjection_fiber_base {W : BigFppfOver B S hS}
    (a : (polarizedSliceProjection B hS hT).Fiber W) : a.1.base = W.left :=
  congrArg Comma.left a.2

/-- The base of the source of a morphism of polarized families lying over `h : W ⟶ W'` is the
underlying scheme of `W`. -/
theorem polarizedSliceProjection_base_eq_of_isHomLift_domain {W W' : BigFppfOver B S hS}
    (h : W ⟶ W') {a b : PolarizedFamily B} (φ : a ⟶ b)
    [(polarizedSliceProjection B hS hT).IsHomLift h φ] : a.base = W.left :=
  congrArg Comma.left (IsHomLift.domain_eq (polarizedSliceProjection B hS hT) h φ)

/-- The base of the target of a morphism of polarized families lying over `h : W ⟶ W'` is the
underlying scheme of `W'`. -/
theorem polarizedSliceProjection_base_eq_of_isHomLift_codomain {W W' : BigFppfOver B S hS}
    (h : W ⟶ W') {a b : PolarizedFamily B} (φ : a ⟶ b)
    [(polarizedSliceProjection B hS hT).IsHomLift h φ] : b.base = W'.left :=
  congrArg Comma.left (IsHomLift.codomain_eq (polarizedSliceProjection B hS hT) h φ)

/-- The base map of a morphism of polarized families lying over `h` is the underlying morphism of
`h`, read through the identifications of the bases with the underlying schemes. -/
theorem polarizedSliceProjection_baseMap_eq {W W' : BigFppfOver B S hS} (h : W ⟶ W')
    {a b : PolarizedFamily B} (φ : a ⟶ b) [(polarizedSliceProjection B hS hT).IsHomLift h φ] :
    φ.baseMap = eqToHom (polarizedSliceProjection_base_eq_of_isHomLift_domain B hS hT h φ) ≫
      h.left ≫
        eqToHom (polarizedSliceProjection_base_eq_of_isHomLift_codomain B hS hT h φ).symm := by
  have e := congrArg CommaMorphism.left
    (IsHomLift.fac' (polarizedSliceProjection B hS hT) h φ)
  change φ.baseMap = _ at e
  simp only [Over.comp_left, Over.eqToHom_left] at e
  exact e

/-- `AlgebraicGeometry.polarizedSliceProjection_baseMap_eq`, read in the category of all
schemes. -/
theorem polarizedSliceProjection_inclusion_map_baseMap_eq {W W' : BigFppfOver B S hS}
    (h : W ⟶ W') {a b : PolarizedFamily B} (φ : a ⟶ b)
    [(polarizedSliceProjection B hS hT).IsHomLift h φ] :
    B.inclusion.map φ.baseMap =
      eqToHom (congrArg B.inclusion.obj
        (polarizedSliceProjection_base_eq_of_isHomLift_domain B hS hT h φ)) ≫
        B.inclusion.map h.left ≫ eqToHom (congrArg B.inclusion.obj
          (polarizedSliceProjection_base_eq_of_isHomLift_codomain B hS hT h φ)).symm := by
  rw [polarizedSliceProjection_baseMap_eq B hS hT h φ, Functor.map_comp, Functor.map_comp,
    eqToHom_map, eqToHom_map]

variable (U : BigFppfOver B S hS)

/-- The chosen pullback of an object `x` of the fibre of `𝒫olarized` over `U` to an object `V` of
the big fppf site of `U`. -/
abbrev polarizedRestriction (x : (polarizedSliceProjection B hS hT).Fiber U)
    (V : BigFppfOver B U.left.obj U.left.property) :
    (polarizedSliceProjection B hS hT).Fiber ((Over.iteratedSliceBackward U).obj V).left :=
  Functor.pullbackFiber (polarizedSliceProjection B hS hT) x
    ((Over.iteratedSliceBackward U).obj V).hom

/-- The restriction map between chosen pullbacks of `x` along a morphism `f : V' ⟶ V` of the big
fppf site of `U`. -/
abbrev polarizedRestrictionMap (x : (polarizedSliceProjection B hS hT).Fiber U)
    {V V' : BigFppfOver B U.left.obj U.left.property} (f : V' ⟶ V) :
    (polarizedRestriction B hS hT U x V').1 ⟶ (polarizedRestriction B hS hT U x V).1 :=
  Functor.pullbackFiberMap (polarizedSliceProjection B hS hT) x
    ((Over.iteratedSliceBackward U).map f)

/-- The presheaf `Mor(x, y)` of Stacks 02ZB of two objects of the fibre of `𝒫olarized` over
`U`, read on the big fppf site of `U`. -/
abbrev polarizedMorPresheaf (x y : (polarizedSliceProjection B hS hT).Fiber U) :
    (BigFppfOver B U.left.obj U.left.property)ᵒᵖ ⥤ Type u :=
  (Over.iteratedSliceBackward U).op ⋙ (polarizedSliceProjection B hS hT).morPresheaf x y

variable {B hS hT U}

/-- **The restriction maps of `Mor(x, y)`.** The restriction of a section `m` along `f` is the
unique morphism `n` of the fibre for which restricting `x` and then applying `m` agrees with
applying `n` and then restricting `y`. -/
theorem polarizedMorPresheaf_map_eq_iff {x y : (polarizedSliceProjection B hS hT).Fiber U}
    {V V' : BigFppfOver B U.left.obj U.left.property} (f : V' ⟶ V)
    (m : polarizedRestriction B hS hT U x V ⟶ polarizedRestriction B hS hT U y V)
    (n : polarizedRestriction B hS hT U x V' ⟶ polarizedRestriction B hS hT U y V') :
    (polarizedMorPresheaf B hS hT U x y).map f.op m = n ↔
      n.1 ≫ polarizedRestrictionMap B hS hT U y f =
        polarizedRestrictionMap B hS hT U x f ≫ m.1 := by
  constructor
  · rintro rfl
    exact Functor.fiberInclusion_map_morRestrict_comp_pullbackFiberMap _ x y
      ((Over.iteratedSliceBackward U).map f) m
  · intro hn
    symm
    refine Functor.morRestrict_uniq _ x y ((Over.iteratedSliceBackward U).map f) m n ?_
    change n.1 ≫ _ = _ ≫ m.1 ≫ _
    rw [← Functor.pullbackFiberMap_fac _ y ((Over.iteratedSliceBackward U).map f),
      ← Category.assoc, hn, Category.assoc]

/-- The restriction maps of the chosen pullbacks of `x` along the two sides of a commutative
square of the big fppf site of `U` agree. -/
theorem polarizedRestrictionMap_comp_eq (x : (polarizedSliceProjection B hS hT).Fiber U)
    {W V₁ V₂ V : BigFppfOver B U.left.obj U.left.property} {a : W ⟶ V₁} {b : W ⟶ V₂}
    {f₁ : V₁ ⟶ V} {f₂ : V₂ ⟶ V} (h : a ≫ f₁ = b ≫ f₂) :
    polarizedRestrictionMap B hS hT U x a ≫ polarizedRestrictionMap B hS hT U x f₁ =
      polarizedRestrictionMap B hS hT U x b ≫ polarizedRestrictionMap B hS hT U x f₂ := by
  rw [Functor.pullbackFiberMap_comp, Functor.pullbackFiberMap_comp, ← Functor.map_comp,
    ← Functor.map_comp, h]

/-- Two sections of `Mor(x, y)` with the same restriction to `W` become equal morphisms of
polarized families once restricted to `W` and pushed to a common target `V`. -/
theorem polarizedRestrictionMap_comp_of_compatible
    {x y : (polarizedSliceProjection B hS hT).Fiber U}
    {W V₁ V₂ V : BigFppfOver B U.left.obj U.left.property} {a : W ⟶ V₁} {b : W ⟶ V₂}
    {f₁ : V₁ ⟶ V} {f₂ : V₂ ⟶ V} (h : a ≫ f₁ = b ≫ f₂)
    (m₁ : polarizedRestriction B hS hT U x V₁ ⟶ polarizedRestriction B hS hT U y V₁)
    (m₂ : polarizedRestriction B hS hT U x V₂ ⟶ polarizedRestriction B hS hT U y V₂)
    (hm : (polarizedMorPresheaf B hS hT U x y).map a.op m₁ =
      (polarizedMorPresheaf B hS hT U x y).map b.op m₂) :
    polarizedRestrictionMap B hS hT U x a ≫ m₁.1 ≫ polarizedRestrictionMap B hS hT U y f₁ =
      polarizedRestrictionMap B hS hT U x b ≫ m₂.1 ≫ polarizedRestrictionMap B hS hT U y f₂ := by
  have h₁ := (polarizedMorPresheaf_map_eq_iff a m₁ _).1 rfl
  have h₂ := (polarizedMorPresheaf_map_eq_iff b m₂ _).1 hm.symm
  rw [← Category.assoc, ← h₁, Category.assoc, polarizedRestrictionMap_comp_eq y h,
    ← Category.assoc, h₂, Category.assoc]

/-- `AlgebraicGeometry.polarizedSliceProjection_inclusion_map_baseMap_eq` for a restriction map of
the chosen pullbacks of `x`. -/
private theorem polarizedRestrictionMap_inclusion_map_baseMap_eq
    (x : (polarizedSliceProjection B hS hT).Fiber U)
    {V V' : BigFppfOver B U.left.obj U.left.property} (f : V' ⟶ V) :
    B.inclusion.map (polarizedRestrictionMap B hS hT U x f).baseMap =
      eqToHom (congrArg B.inclusion.obj
        (polarizedSliceProjection_base_eq_of_isHomLift_domain B hS hT
          ((Over.iteratedSliceBackward U).map f).left (polarizedRestrictionMap B hS hT U x f))) ≫
        B.inclusion.map ((Over.iteratedSliceBackward U).map f).left.left ≫
        eqToHom (congrArg B.inclusion.obj
          (polarizedSliceProjection_base_eq_of_isHomLift_codomain B hS hT
            ((Over.iteratedSliceBackward U).map f).left
            (polarizedRestrictionMap B hS hT U x f))).symm :=
  polarizedSliceProjection_inclusion_map_baseMap_eq B hS hT _ _

/-- The base maps of the restriction maps of `x` along an fppf covering family of the big fppf
site of `U` form an fppf covering family of schemes. -/
theorem ofArrows_polarizedRestrictionMap_baseMap_mem_fppfPrecoverage
    (x : (polarizedSliceProjection B hS hT).Fiber U)
    {ι : Type*} {V₀ : BigFppfOver B U.left.obj U.left.property}
    {V : ι → BigFppfOver B U.left.obj U.left.property} (f : ∀ i, V i ⟶ V₀)
    (hf : Presieve.ofArrows (fun i => B.inclusion.obj (V i).left)
      (fun i => B.inclusion.map (f i).left) ∈
        Scheme.fppfPrecoverage.{u} (B.inclusion.obj V₀.left)) :
    Presieve.ofArrows (fun i => B.inclusion.obj (polarizedRestriction B hS hT U x (V i)).1.base)
      (fun i => B.inclusion.map (polarizedRestrictionMap B hS hT U x (f i)).baseMap) ∈
        Scheme.fppfPrecoverage.{u}
          (B.inclusion.obj (polarizedRestriction B hS hT U x V₀).1.base) := by
  rw [funext fun i => polarizedRestrictionMap_inclusion_map_baseMap_eq x (f i)]
  exact Presieve.ofArrows_eqToHom_mem _
    (congrArg B.inclusion.obj (polarizedSliceProjection_fiber_base B hS hT
      (polarizedRestriction B hS hT U x V₀))).symm
    (fun i => congrArg B.inclusion.obj
      (polarizedSliceProjection_fiber_base B hS hT (polarizedRestriction B hS hT U x (V i)))) hf

/-- **The total spaces of the restrictions of `x` along an fppf covering family of the big fppf
site of `U` form an fpqc covering of the total space of the restriction to the target.** -/
theorem ofArrows_polarizedRestrictionMap_totalMap_mem_fpqcPrecoverage
    (x : (polarizedSliceProjection B hS hT).Fiber U)
    {ι : Type*} {V₀ : BigFppfOver B U.left.obj U.left.property}
    {V : ι → BigFppfOver B U.left.obj U.left.property} (f : ∀ i, V i ⟶ V₀)
    (hf : Presieve.ofArrows (fun i => B.inclusion.obj (V i).left)
      (fun i => B.inclusion.map (f i).left) ∈
        Scheme.fppfPrecoverage.{u} (B.inclusion.obj V₀.left)) :
    Presieve.ofArrows (fun i => (polarizedRestriction B hS hT U x (V i)).1.total)
      (fun i => (polarizedRestrictionMap B hS hT U x (f i)).totalMap) ∈
        Scheme.fpqcPrecoverage.{u} (polarizedRestriction B hS hT U x V₀).1.total :=
  Scheme.fppfPrecoverage_le_fpqcPrecoverage _
    (PolarizedFamily.ofArrows_totalMap_mem_fppfPrecoverage _
      (ofArrows_polarizedRestrictionMap_baseMap_mem_fppfPrecoverage x f hf))

/-- **A scheme mapping compatibly to the total spaces of two restrictions of `x` lifts to the
total space of the restriction to the fibre product.** This is what reduces compatibility of
maps out of total spaces on arbitrary schemes to compatibility over objects of the site: the
square of bases of the restrictions is a pullback because the fibre product of the site is one
of schemes, and the squares of total spaces over it are cartesian. -/
theorem exists_lift_polarizedRestriction (x : (polarizedSliceProjection B hS hT).Fiber U)
    {V₁ V₂ V : BigFppfOver B U.left.obj U.left.property} (f₁ : V₁ ⟶ V) (f₂ : V₂ ⟶ V)
    [HasPullback f₁ f₂] {Z : Scheme.{u}}
    (g₁ : Z ⟶ (polarizedRestriction B hS hT U x V₁).1.total)
    (g₂ : Z ⟶ (polarizedRestriction B hS hT U x V₂).1.total)
    (h : g₁ ≫ (polarizedRestrictionMap B hS hT U x f₁).totalMap =
      g₂ ≫ (polarizedRestrictionMap B hS hT U x f₂).totalMap) :
    ∃ z : Z ⟶ (polarizedRestriction B hS hT U x (pullback f₁ f₂)).1.total,
      z ≫ (polarizedRestrictionMap B hS hT U x (pullback.fst f₁ f₂)).totalMap = g₁ ∧
        z ≫ (polarizedRestrictionMap B hS hT U x (pullback.snd f₁ f₂)).totalMap = g₂ := by
  have := preservesPullbacks_bigFppfOverToScheme B U.left.obj U.left.property
  have hpbS := (IsPullback.of_hasPullback f₁ f₂).map
    (BigFppfOver.toScheme B U.left.obj U.left.property)
  have hbase : IsPullback
      (B.inclusion.map (polarizedRestrictionMap B hS hT U x (pullback.fst f₁ f₂)).baseMap)
      (B.inclusion.map (polarizedRestrictionMap B hS hT U x (pullback.snd f₁ f₂)).baseMap)
      (B.inclusion.map (polarizedRestrictionMap B hS hT U x f₁).baseMap)
      (B.inclusion.map (polarizedRestrictionMap B hS hT U x f₂).baseMap) := by
    rw [polarizedRestrictionMap_inclusion_map_baseMap_eq x (pullback.fst f₁ f₂),
      polarizedRestrictionMap_inclusion_map_baseMap_eq x (pullback.snd f₁ f₂),
      polarizedRestrictionMap_inclusion_map_baseMap_eq x f₁,
      polarizedRestrictionMap_inclusion_map_baseMap_eq x f₂]
    exact hpbS.eqToHom_conj _ _ _ _
  set c₁ := polarizedRestrictionMap B hS hT U x f₁
  set c₂ := polarizedRestrictionMap B hS hT U x f₂
  set ca := polarizedRestrictionMap B hS hT U x (pullback.fst f₁ f₂)
  set cb := polarizedRestrictionMap B hS hT U x (pullback.snd f₁ f₂)
  have hw : (g₁ ≫ (polarizedRestriction B hS hT U x V₁).1.toBase) ≫
      B.inclusion.map c₁.baseMap =
      (g₂ ≫ (polarizedRestriction B hS hT U x V₂).1.toBase) ≫ B.inclusion.map c₂.baseMap := by
    rw [Category.assoc, Category.assoc, ← c₁.cartesian.w, ← c₂.cartesian.w,
      ← Category.assoc, h, Category.assoc]
  let ζ := hbase.lift _ _ hw
  let z := ca.cartesian.lift g₁ ζ (hbase.lift_fst _ _ hw).symm
  have hz₁ : z ≫ ca.totalMap = g₁ := ca.cartesian.lift_fst _ _ _
  have hz₀ : z ≫ (polarizedRestriction B hS hT U x (pullback f₁ f₂)).1.toBase = ζ :=
    ca.cartesian.lift_snd _ _ _
  have hcomm : ca ≫ c₁ = cb ≫ c₂ := polarizedRestrictionMap_comp_eq x pullback.condition
  refine ⟨z, hz₁, c₂.cartesian.hom_ext ?_ ?_⟩
  · rw [Category.assoc, ← PolarizedFamily.comp_totalMap, ← hcomm,
      PolarizedFamily.comp_totalMap, ← Category.assoc, hz₁, h]
  · rw [Category.assoc, cb.cartesian.w, ← Category.assoc, hz₀, hbase.lift_snd]

/-- **The maps of total spaces of a compatible family of `Mor(x, y)` are compatible on every
scheme.** Composed with the restriction maps of `y`, they agree on every scheme mapping
compatibly to two members of the covering. -/
theorem polarizedRestriction_totalMap_comp_eq_of_compatible
    {x y : (polarizedSliceProjection B hS hT).Fiber U}
    {ι : Type*} {V₀ : BigFppfOver B U.left.obj U.left.property}
    {V : ι → BigFppfOver B U.left.obj U.left.property} (f : ∀ i, V i ⟶ V₀)
    (m : ∀ i, polarizedRestriction B hS hT U x (V i) ⟶ polarizedRestriction B hS hT U y (V i))
    (hm : Presieve.Arrows.Compatible (polarizedMorPresheaf B hS hT U x y) f m) (i j : ι)
    {Z : Scheme.{u}} (g₁ : Z ⟶ (polarizedRestriction B hS hT U x (V i)).1.total)
    (g₂ : Z ⟶ (polarizedRestriction B hS hT U x (V j)).1.total)
    (h : g₁ ≫ (polarizedRestrictionMap B hS hT U x (f i)).totalMap =
      g₂ ≫ (polarizedRestrictionMap B hS hT U x (f j)).totalMap) :
    g₁ ≫ ((m i).1 ≫ polarizedRestrictionMap B hS hT U y (f i)).totalMap =
      g₂ ≫ ((m j).1 ≫ polarizedRestrictionMap B hS hT U y (f j)).totalMap := by
  have := hasPullbacks_bigFppfOver B U.left.obj U.left.property
  obtain ⟨z, rfl, rfl⟩ := exists_lift_polarizedRestriction x (f i) (f j) g₁ g₂ h
  have hc := polarizedRestrictionMap_comp_of_compatible pullback.condition (m i) (m j)
    (hm i j _ (pullback.fst (f i) (f j)) (pullback.snd (f i) (f j)) pullback.condition)
  rw [Category.assoc, Category.assoc, ← PolarizedFamily.comp_totalMap,
    ← PolarizedFamily.comp_totalMap, hc]

/-- **The comparisons of polarizations of a compatible family of `Mor(x, y)` are compatible on
every scheme**, in the form
`AlgebraicGeometry.PolarizedFamily.Hom.exists_comp_eq_of_mem_fpqcPrecoverage` consumes. -/
theorem polarizedRestriction_canStep_lineBundleComparison_eq_of_compatible
    {x y : (polarizedSliceProjection B hS hT).Fiber U}
    {ι : Type*} {V₀ : BigFppfOver B U.left.obj U.left.property}
    {V : ι → BigFppfOver B U.left.obj U.left.property} (f : ∀ i, V i ⟶ V₀)
    (m : ∀ i, polarizedRestriction B hS hT U x (V i) ⟶ polarizedRestriction B hS hT U y (V i))
    (hm : Presieve.Arrows.Compatible (polarizedMorPresheaf B hS hT U x y) f m)
    (M : (polarizedRestriction B hS hT U x V₀).1.total ⟶
      (polarizedRestriction B hS hT U y V₀).1.total)
    (hM : ∀ i, (polarizedRestrictionMap B hS hT U x (f i)).totalMap ≫ M =
      ((m i).1 ≫ polarizedRestrictionMap B hS hT U y (f i)).totalMap)
    {Z : Scheme.{u}} (k : Z ⟶ (polarizedRestriction B hS hT U x V₀).1.total) (i j : ι)
    (g₁ : Z ⟶ (polarizedRestriction B hS hT U x (V i)).1.total)
    (g₂ : Z ⟶ (polarizedRestriction B hS hT U x (V j)).1.total)
    (h₁ : g₁ ≫ (polarizedRestrictionMap B hS hT U x (f i)).totalMap = k)
    (h₂ : g₂ ≫ (polarizedRestrictionMap B hS hT U x (f j)).totalMap = k) :
    canStep g₁ (polarizedRestrictionMap B hS hT U x (f i)).totalMap k h₁
        (PolarizedFamily.lineBundleComparison (polarizedRestrictionMap B hS hT U x (f i))
          ((m i).1 ≫ polarizedRestrictionMap B hS hT U y (f i)) M (hM i)) =
      canStep g₂ (polarizedRestrictionMap B hS hT U x (f j)).totalMap k h₂
        (PolarizedFamily.lineBundleComparison (polarizedRestrictionMap B hS hT U x (f j))
          ((m j).1 ≫ polarizedRestrictionMap B hS hT U y (f j)) M (hM j)) := by
  have := hasPullbacks_bigFppfOver B U.left.obj U.left.property
  obtain ⟨z, rfl, rfl⟩ :=
    exists_lift_polarizedRestriction x (f i) (f j) g₁ g₂ (h₁.trans h₂.symm)
  have hc := polarizedRestrictionMap_comp_of_compatible pullback.condition (m i) (m j)
    (hm i j _ (pullback.fst (f i) (f j)) (pullback.snd (f i) (f j)) pullback.condition)
  have hcx := polarizedRestrictionMap_comp_eq x (pullback.condition (f := f i) (g := f j))
  rw [← canStep_canStep z
      (polarizedRestrictionMap B hS hT U x (pullback.fst (f i) (f j))).totalMap
      (polarizedRestrictionMap B hS hT U x (f i)).totalMap _
      (polarizedRestrictionMap B hS hT U x (pullback.fst (f i) (f j)) ≫
        polarizedRestrictionMap B hS hT U x (f i)).totalMap k rfl
      (PolarizedFamily.comp_totalMap _ _).symm
      (by rw [PolarizedFamily.comp_totalMap, ← Category.assoc]; exact h₁) h₁,
    ← canStep_canStep z
      (polarizedRestrictionMap B hS hT U x (pullback.snd (f i) (f j))).totalMap
      (polarizedRestrictionMap B hS hT U x (f j)).totalMap _
      (polarizedRestrictionMap B hS hT U x (pullback.snd (f i) (f j)) ≫
        polarizedRestrictionMap B hS hT U x (f j)).totalMap k rfl
      (PolarizedFamily.comp_totalMap _ _).symm
      (by rw [PolarizedFamily.comp_totalMap, ← Category.assoc]; exact h₂) h₂,
    PolarizedFamily.canStep_lineBundleComparison, PolarizedFamily.canStep_lineBundleComparison]
  have key : ∀ (c c' : (polarizedRestriction B hS hT U x (pullback (f i) (f j))).1 ⟶
      (polarizedRestriction B hS hT U x V₀).1)
      (ψ ψ' : (polarizedRestriction B hS hT U x (pullback (f i) (f j))).1 ⟶
        (polarizedRestriction B hS hT U y V₀).1), c = c' → ψ = ψ' →
      ∀ h₁ h₂ h₃ h₄, canStep z c.totalMap k h₁ (PolarizedFamily.lineBundleComparison c ψ M h₂) =
        canStep z c'.totalMap k h₃ (PolarizedFamily.lineBundleComparison c' ψ' M h₄) := by
    rintro c _ ψ _ rfl rfl _ _ _ _
    rfl
  exact key _ _ _ _ hcx hc _ _ _ _

/-- The base maps of a section of `Mor(x, y)` composed with a restriction map of `y` factor
through the identification of the bases of the restrictions of `x` and `y` to the target. -/
theorem polarizedRestrictionMap_baseMap_comp_eqToHom
    {x y : (polarizedSliceProjection B hS hT).Fiber U}
    {V V₀ : BigFppfOver B U.left.obj U.left.property} (f : V ⟶ V₀)
    (m : polarizedRestriction B hS hT U x V ⟶ polarizedRestriction B hS hT U y V) :
    (polarizedRestrictionMap B hS hT U x f).baseMap ≫
        eqToHom ((polarizedSliceProjection_fiber_base B hS hT
          (polarizedRestriction B hS hT U x V₀)).trans
          (polarizedSliceProjection_fiber_base B hS hT
            (polarizedRestriction B hS hT U y V₀)).symm) =
      (m.1 ≫ polarizedRestrictionMap B hS hT U y f).baseMap := by
  have := m.2
  rw [PolarizedFamily.comp_baseMap,
    polarizedSliceProjection_baseMap_eq B hS hT ((Over.iteratedSliceBackward U).map f).left
      (polarizedRestrictionMap B hS hT U x f),
    polarizedSliceProjection_baseMap_eq B hS hT ((Over.iteratedSliceBackward U).map f).left
      (polarizedRestrictionMap B hS hT U y f),
    polarizedSliceProjection_baseMap_eq B hS hT
      (𝟙 ((Over.iteratedSliceBackward U).obj V).left) m.1]
  exact eqToHom_comp_comp_eqToHom_eq _ _ _ _ _ _ _ _

/-- A morphism of polarized families between two objects of the fibre over `W` lies over the
identity of `W` as soon as its base map is the identification of the two bases. -/
theorem polarizedSliceProjection_isHomLift_id_of_baseMap_eq {W : BigFppfOver B S hS}
    (a b : (polarizedSliceProjection B hS hT).Fiber W) (χ : a.1 ⟶ b.1)
    (hχ : χ.baseMap = eqToHom ((polarizedSliceProjection_fiber_base B hS hT a).trans
      (polarizedSliceProjection_fiber_base B hS hT b).symm)) :
    (polarizedSliceProjection B hS hT).IsHomLift (𝟙 W) χ := by
  refine IsHomLift.of_fac' _ _ _ a.2 b.2 ?_
  apply Over.OverMorphism.ext
  change χ.baseMap = _
  rw [hχ]
  simp only [Over.eqToHom_left, Category.id_comp, eqToHom_trans]
  rfl

/-- **The sheaf condition for `Mor(x, y)` along an fppf covering family.** For a family of the
big fppf site of `U` whose underlying morphisms of schemes form an fppf covering, `Mor(x, y)`
satisfies the sheaf condition. -/
theorem isSheafFor_polarizedMorPresheaf (x y : (polarizedSliceProjection B hS hT).Fiber U)
    {ι : Type*} {V₀ : BigFppfOver B U.left.obj U.left.property}
    {V : ι → BigFppfOver B U.left.obj U.left.property} (f : ∀ i, V i ⟶ V₀)
    (hf : Presieve.ofArrows (fun i => B.inclusion.obj (V i).left)
      (fun i => B.inclusion.map (f i).left) ∈
        Scheme.fppfPrecoverage.{u} (B.inclusion.obj V₀.left)) :
    Presieve.IsSheafFor (polarizedMorPresheaf B hS hT U x y) (Presieve.ofArrows V f) := by
  have hp : (polarizedSliceProjection B hS hT).IsFiberedInGroupoids :=
    polarizedProjection_isFiberedInGroupoids_unconditional.sliceAtTerminal hT
  have hgrp := fun W => hp.fiber_isGroupoid W
  rw [Presieve.isSheafFor_arrows_iff]
  intro m₀ hm
  let m : ∀ i, polarizedRestriction B hS hT U x (V i) ⟶ polarizedRestriction B hS hT U y (V i) :=
    m₀
  have hcx := ofArrows_polarizedRestrictionMap_totalMap_mem_fpqcPrecoverage x f hf
  have hcy := ofArrows_polarizedRestrictionMap_totalMap_mem_fpqcPrecoverage y f hf
  obtain ⟨M, hM, -⟩ := Scheme.existsUnique_comp_eq_of_mem_fpqcPrecoverage _ hcx
    (fun i => ((m i).1 ≫ polarizedRestrictionMap B hS hT U y (f i)).totalMap)
    (fun i j Z g₁ g₂ h => polarizedRestriction_totalMap_comp_eq_of_compatible f m hm i j g₁ g₂ h)
  let m' : ∀ i, polarizedRestriction B hS hT U y (V i) ⟶ polarizedRestriction B hS hT U x (V i) :=
    fun i => inv (m i)
  have hinv : ∀ {W V' : BigFppfOver B U.left.obj U.left.property} (g : W ⟶ V')
      (n : polarizedRestriction B hS hT U x V' ⟶ polarizedRestriction B hS hT U y V'),
      (polarizedMorPresheaf B hS hT U y x).map g.op (inv n) =
        inv ((polarizedMorPresheaf B hS hT U x y).map g.op n) := by
    intro W V' g n
    refine IsIso.eq_inv_of_inv_hom_id ?_
    change Functor.morRestrict _ y x _ (inv n) ≫ Functor.morRestrict _ x y _ n = 𝟙 _
    rw [← Functor.morRestrict_comp_hom, IsIso.inv_hom_id, Functor.morRestrict_id_hom]
  have hm' : Presieve.Arrows.Compatible (polarizedMorPresheaf B hS hT U y x) f m' := by
    intro i j Z g₁ g₂ h
    change (polarizedMorPresheaf B hS hT U y x).map g₁.op (inv (m i)) =
      (polarizedMorPresheaf B hS hT U y x).map g₂.op (inv (m j))
    rw [hinv, hinv]
    exact IsIso.inv_eq_inv.mpr (hm i j Z g₁ g₂ h)
  obtain ⟨N, hN, -⟩ := Scheme.existsUnique_comp_eq_of_mem_fpqcPrecoverage _ hcy
    (fun i => ((m' i).1 ≫ polarizedRestrictionMap B hS hT U x (f i)).totalMap)
    (fun i j Z g₁ g₂ h =>
      polarizedRestriction_totalMap_comp_eq_of_compatible f m' hm' i j g₁ g₂ h)
  have hmi : ∀ i, (m i).1 ≫ (m' i).1 = 𝟙 _ := fun i =>
    congrArg Subtype.val (IsIso.hom_inv_id (m i))
  have hmi' : ∀ i, (m' i).1 ≫ (m i).1 = 𝟙 _ := fun i =>
    congrArg Subtype.val (IsIso.inv_hom_id (m i))
  have hMN : M ≫ N = 𝟙 _ := hom_ext_of_mem_fpqcPrecoverage _ hcx fun i => by
    rw [← Category.assoc, hM i, PolarizedFamily.comp_totalMap, Category.assoc, hN i,
      PolarizedFamily.comp_totalMap, ← Category.assoc, ← PolarizedFamily.comp_totalMap, hmi i,
      PolarizedFamily.id_totalMap, Category.id_comp, Category.comp_id]
  have hNM : N ≫ M = 𝟙 _ := hom_ext_of_mem_fpqcPrecoverage _ hcy fun i => by
    rw [← Category.assoc, hN i, PolarizedFamily.comp_totalMap, Category.assoc, hM i,
      PolarizedFamily.comp_totalMap, ← Category.assoc, ← PolarizedFamily.comp_totalMap, hmi' i,
      PolarizedFamily.id_totalMap, Category.id_comp, Category.comp_id]
  have : IsIso M := ⟨⟨N, hMN, hNM⟩⟩
  let β₀ : (polarizedRestriction B hS hT U x V₀).1.base ⟶
      (polarizedRestriction B hS hT U y V₀).1.base :=
    eqToHom ((polarizedSliceProjection_fiber_base B hS hT
      (polarizedRestriction B hS hT U x V₀)).trans
      (polarizedSliceProjection_fiber_base B hS hT (polarizedRestriction B hS hT U y V₀)).symm)
  have hbase : ∀ i, (polarizedRestrictionMap B hS hT U x (f i)).baseMap ≫ β₀ =
      ((m i).1 ≫ polarizedRestrictionMap B hS hT U y (f i)).baseMap := fun i =>
    polarizedRestrictionMap_baseMap_comp_eqToHom (f i) (m i)
  have hcomm : M ≫ (polarizedRestriction B hS hT U y V₀).1.toBase =
      (polarizedRestriction B hS hT U x V₀).1.toBase ≫ B.inclusion.map β₀ :=
    hom_ext_of_mem_fpqcPrecoverage _ hcx fun i => by
      rw [← Category.assoc, hM i,
        ((m i).1 ≫ polarizedRestrictionMap B hS hT U y (f i)).cartesian.w, ← hbase i,
        Functor.map_comp, ← Category.assoc,
        ← (polarizedRestrictionMap B hS hT U x (f i)).cartesian.w, Category.assoc]
  have hcart : IsPullback M (polarizedRestriction B hS hT U x V₀).1.toBase
      (polarizedRestriction B hS hT U y V₀).1.toBase (B.inclusion.map β₀) :=
    IsPullback.of_horiz_isIso ⟨hcomm⟩
  obtain ⟨χ, hχb, -, hχ⟩ := PolarizedFamily.Hom.exists_comp_eq_of_mem_fpqcPrecoverage
    (fun i => polarizedRestrictionMap B hS hT U x (f i)) hcx
    (fun i => (m i).1 ≫ polarizedRestrictionMap B hS hT U y (f i)) β₀ hbase M hM hcart
    (fun Z k i j g₁ g₂ h₁ h₂ =>
      polarizedRestriction_canStep_lineBundleComparison_eq_of_compatible f m hm M hM k i j
        g₁ g₂ h₁ h₂)
  let t : polarizedRestriction B hS hT U x V₀ ⟶ polarizedRestriction B hS hT U y V₀ :=
    ⟨χ, polarizedSliceProjection_isHomLift_id_of_baseMap_eq _ _ χ hχb⟩
  refine ⟨t, fun i => (polarizedMorPresheaf_map_eq_iff (f i) t (m i)).2 (hχ i).symm,
    fun t' ht' => ?_⟩
  apply Functor.Fiber.hom_ext
  refine PolarizedFamily.Hom.ext_of_comp_eq_of_mem_fpqcPrecoverage _ hcx ?_ fun i => ?_
  · have : (polarizedSliceProjection B hS hT).IsHomLift
        (𝟙 ((Over.iteratedSliceBackward U).obj V₀).left) t'.1 := t'.2
    change t'.1.baseMap = χ.baseMap
    rw [polarizedSliceProjection_baseMap_eq B hS hT
      (𝟙 ((Over.iteratedSliceBackward U).obj V₀).left) t'.1, hχb]
    simp only [Over.id_left, Category.id_comp, eqToHom_trans]
    rfl
  · change _ ≫ t'.1 = _ ≫ χ
    rw [← (polarizedMorPresheaf_map_eq_iff (f i) t' (m i)).1 (ht' i), hχ i]

/-- **`Mor(x, y)` is an fppf sheaf on the big fppf site of `U`.** -/
theorem isSheaf_polarizedMorPresheaf (x y : (polarizedSliceProjection B hS hT).Fiber U) :
    Presheaf.IsSheaf (BigFppfOver.topology B U.left.obj U.left.property)
      (polarizedMorPresheaf B hS hT U x y) := by
  refine BigFppfOver.isSheaf_of_isSheafFor_isCovering B _ _ fun V₀ E hE => ?_
  have h : (E.map (BigFppfOver.forget B U.left.obj U.left.property)).presieve₀ ∈
      Scheme.fppfPrecoverage.comap B.inclusion V₀.left := B.isFppfCovering_of_isCovering hE
  rw [Precoverage.mem_comap_iff, ← PreZeroHypercover.presieve₀_map] at h
  exact isSheafFor_polarizedMorPresheaf x y E.f h

end Polarized

/-! ### The isomorphism presheaf -/

variable (B : BigFppfSite.{u}) {S : Scheme.{u}} (hS : B.Contains S)
  (hT : Limits.IsTerminal (B.obj hS))

/-- The isomorphism presheaf of two objects of the fibre of `𝒫olarized` over `U`, read on the
big fppf site of `U` (the presheaf of condition (2) of Stacks 045G). -/
noncomputable abbrev polarizedIsomPresheaf (U : BigFppfOver B S hS)
    (x y : (polarizedStackUnconditional B hS hT).val.p.Fiber U) :
    (BigFppfOver B U.left.obj U.left.property)ᵒᵖ ⥤ Type u :=
  (Over.iteratedSliceBackward U).op ⋙ (polarizedStackUnconditional B hS hT).val.p.isomPresheaf x y

/-- **The isomorphism presheaf `Isom(x, y)` of two polarized families over `U` is an fppf
sheaf.** The fibres of `𝒫olarized` are groupoids, so `Isom(x, y)` is `Mor(x, y)`, which is a
sheaf by `AlgebraicGeometry.isSheaf_polarizedMorPresheaf`. -/
theorem isSheaf_polarizedIsomPresheaf (U : BigFppfOver B S hS)
    (x y : (polarizedStackUnconditional B hS hT).val.p.Fiber U) :
    Presheaf.IsSheaf (BigFppfOver.topology B U.left.obj U.left.property)
      (polarizedIsomPresheaf B hS hT U x y) :=
  (Presheaf.isSheaf_of_iso_iff (Functor.isoWhiskerLeft (Over.iteratedSliceBackward U).op
    (Stack.isomPresheafIsoMorPresheaf (polarizedSliceProjection B hS hT)
      (polarizedProjection_isFiberedInGroupoids_unconditional.sliceAtTerminal hT) x y))).2
    (isSheaf_polarizedMorPresheaf x y)

/-- **The sections of `Isom(x, y)` over `V`** are the morphisms of the fibre of `𝒫olarized` over
`V` between the chosen pullbacks `AlgebraicGeometry.polarizedRestriction` of `x` and `y`; every
such morphism is invertible, the fibre being a groupoid. -/
noncomputable def polarizedIsomPresheafObjEquiv (U : BigFppfOver B S hS)
    (x y : (polarizedStackUnconditional B hS hT).val.p.Fiber U)
    (V : BigFppfOver B U.left.obj U.left.property) :
    (polarizedIsomPresheaf B hS hT U x y).obj (op V) ≃
      (polarizedRestriction B hS hT U x V ⟶ polarizedRestriction B hS hT U y V) :=
  ((Stack.isomPresheafIsoMorPresheaf (polarizedSliceProjection B hS hT)
    (polarizedProjection_isFiberedInGroupoids_unconditional.sliceAtTerminal hT) x y).app
      (op ((Over.iteratedSliceBackward U).obj V))).toEquiv

/-- `AlgebraicGeometry.polarizedIsomPresheafObjEquiv` forgets that a section is an
isomorphism. -/
theorem polarizedIsomPresheafObjEquiv_apply (U : BigFppfOver B S hS)
    (x y : (polarizedStackUnconditional B hS hT).val.p.Fiber U)
    (V : BigFppfOver B U.left.obj U.left.property)
    (s : (polarizedIsomPresheaf B hS hT U x y).obj (op V)) :
    polarizedIsomPresheafObjEquiv B hS hT U x y V s = s.1 :=
  rfl

/-- `AlgebraicGeometry.polarizedIsomPresheafObjEquiv` carries the restriction maps of `Isom(x, y)`
to those of `Mor(x, y)`. -/
theorem polarizedIsomPresheafObjEquiv_map (U : BigFppfOver B S hS)
    (x y : (polarizedStackUnconditional B hS hT).val.p.Fiber U)
    {V V' : BigFppfOver B U.left.obj U.left.property} (f : V' ⟶ V)
    (s : (polarizedIsomPresheaf B hS hT U x y).obj (op V)) :
    polarizedIsomPresheafObjEquiv B hS hT U x y V'
        ((polarizedIsomPresheaf B hS hT U x y).map f.op s) =
      (polarizedMorPresheaf B hS hT U x y).map f.op
        (polarizedIsomPresheafObjEquiv B hS hT U x y V s) :=
  rfl

/-- **The restriction maps of `Isom(x, y)`.** The restriction along `f : V' ⟶ V` of a section `s`
is the section `s'` for which restricting `x` along `f` and then applying `s` agrees with
applying `s'` and then restricting `y` along `f`, as morphisms of polarized families. -/
theorem polarizedIsomPresheaf_map_eq_iff (U : BigFppfOver B S hS)
    (x y : (polarizedStackUnconditional B hS hT).val.p.Fiber U)
    {V V' : BigFppfOver B U.left.obj U.left.property} (f : V' ⟶ V)
    (s : (polarizedIsomPresheaf B hS hT U x y).obj (op V))
    (s' : (polarizedIsomPresheaf B hS hT U x y).obj (op V')) :
    (polarizedIsomPresheaf B hS hT U x y).map f.op s = s' ↔
      (polarizedIsomPresheafObjEquiv B hS hT U x y V' s').1 ≫
          polarizedRestrictionMap B hS hT U y f =
        polarizedRestrictionMap B hS hT U x f ≫
          (polarizedIsomPresheafObjEquiv B hS hT U x y V s).1 := by
  rw [← (polarizedIsomPresheafObjEquiv B hS hT U x y V').injective.eq_iff,
    polarizedIsomPresheafObjEquiv_map]
  exact polarizedMorPresheaf_map_eq_iff f _ _

/-- **A morphism of the fibre of `𝒫olarized` over `W`** between `a` and `b` is a morphism of
polarized families `a ⟶ b` whose base map is the identification of the two bases with the
underlying scheme of `W`: a cartesian square over the identity together with a comparison of
polarizations. -/
def polarizedFiberHomEquiv {W : BigFppfOver B S hS}
    (a b : (polarizedSliceProjection B hS hT).Fiber W) :
    (a ⟶ b) ≃ {χ : a.1 ⟶ b.1 // χ.baseMap =
      eqToHom ((polarizedSliceProjection_fiber_base B hS hT a).trans
        (polarizedSliceProjection_fiber_base B hS hT b).symm)} where
  toFun χ := ⟨χ.1, by
    have : (polarizedSliceProjection B hS hT).IsHomLift (𝟙 W) χ.1 := χ.2
    rw [polarizedSliceProjection_baseMap_eq B hS hT (𝟙 W) χ.1]
    simp only [Over.id_left, Category.id_comp, eqToHom_trans]⟩
  invFun χ := ⟨χ.1, polarizedSliceProjection_isHomLift_id_of_baseMap_eq a b χ.1 χ.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

end AlgebraicGeometry

end
