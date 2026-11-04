module

public import StacksFrontier.AlgebraicGeometry.Duality.OpenImmersion.SheafHomRestrictionComp
public import StacksFrontier.AlgebraicGeometry.Duality.RelativeDualizingComplexDiagonalGenerator
public import StacksFrontier.AlgebraicGeometry.Duality.RelativeDualizingComplexRestrictDiagonal
public import StacksFrontier.AlgebraicGeometry.Modules.DerivedPullbackOpensHomGlueing

/-!
# Restricting `ξ` to opens is compatible with shrinking the open

Let `f : X ⟶ S` be a morphism of schemes, `W` a diagonal open of `f` and
`ζ : Δ_*𝒪_X ⟶ L pr₁^*M|_W` in `D(𝒪_W)`. For an open `U` of `X` the restriction of `ζ` to the
restricted diagonal open `W_U ⊆ U ×_S U` is
`Δ_{U*}𝒪_U ≅ Lj_W^*(Δ_*𝒪_X) ⟶ Lj_W^*(L pr₁^*M|_W) ≅ L pr₁^*(M|_U)|_{W_U}`
(`restrictXi`, from the proof of Stacks 0E2X). This file shows that this restriction is natural
in `M` and compatible with shrinking `U`: for opens `V ⊆ U`, if the restrictions of `ζ_M` and
`ζ_N` to `U` are related by `φ : M|_U ⟶ N|_U`, their restrictions to `V` are related by the
restriction of `φ` to `V`. These are the inputs `hnat` and `hle` of the glueing of local
isomorphisms of relative dualizing complexes (Stacks 0E2W).

## Main definitions

* `AlgebraicGeometry.Scheme.Hom.DiagonalOpen.restrictMapOfLE`: the map `W_V ⟶ W_U`.
* `AlgebraicGeometry.Scheme.Hom.DiagonalOpen.restrictXiProj`: `restrictXi` at the inclusion of
  an open, read in the spelling of `derivedPullbackProj`.

## Main results

* `AlgebraicGeometry.Scheme.Hom.DiagonalOpen.restrictXiProj_comp_derivedPullbackProjMap`:
  naturality in the object.
* `AlgebraicGeometry.Scheme.Hom.DiagonalOpen.restrictXiProj_comp_derivedPullbackProjMap_of_le`:
  compatibility with shrinking the open.
* `AlgebraicGeometry.Scheme.Hom.IsRelativeDualizingComplex.restrictProj`: the restriction of a
  relative dualizing complex to an open, with `ξ` restricted by `restrictXiProj`.

## Implementation notes

The restriction from `U` to `V` factors through `W_V ⟶ W_U`, and the comparison of the two
ways of restricting `L pr₁^*M|_W` to `W_V` is a coherence of the composition isomorphisms of
derived pullback (three instances of the cocycle identity of Stacks 0D5S,
`pullCompIso_assoc`). No compatibility of `Lj_W^*(Δ_*𝒪_X) ≅ Δ_{U*}𝒪_U` with multiplications is
needed. The ingredients live in two spellings of the derived categories (`Std` with `pull`,
and `DerivedCategory (OXMod _)` with `derivedPullback`); the chases are generic lemmas in which
every object is a variable, closed with `exact`, and statements are given in the second
spelling, which is that of `IsRelativeDualizingComplex`.

## References

* [Stacks Project, Lemma 48.28.4 (Tag 0E2W)](https://stacks.math.columbia.edu/tag/0E2W)
* [Stacks Project, Lemma 48.28.6 (Tag 0E2X)](https://stacks.math.columbia.edu/tag/0E2X)
* [Stacks Project, Tag 0D5S](https://stacks.math.columbia.edu/tag/0D5S)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits StrictlyPerfect
open Stacks.Duality.TwistedInverseImageDuality
open Stacks.Duality.UpperShriekDuality (pullCompIso)
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces (derivedPullback)
open AlgebraicGeometry.Scheme.DerivedPullbackOpensGlueing

universe u

namespace Stacks.Duality.RelativeDualizingRestrictLE

variable {𝒞 𝒞' 𝒱 𝒱' : Type*} [Category 𝒞] [Category 𝒞'] [Category 𝒱] [Category 𝒱']

/-- The composition isomorphisms of a square of derived pullbacks, by three cocycle
identities, with every object a variable. -/
theorem comp_cocycle_chase (G : 𝒞' ⥤ 𝒞) (P : 𝒱 ⥤ 𝒞) {a b q : 𝒞'} {x y w : 𝒞} {l m : 𝒱}
    (α : G.obj a ⟶ x) (c₁ : x ⟶ y) (c₂ : P.obj m ≅ y) (c₃ : a ⟶ q)
    (c₄ : b ≅ q) (c₈ : G.obj q ⟶ y) (c₅ : G.obj b ⟶ w) (c₆ : P.obj l ≅ w) (c₇ : l ⟶ m)
    (c₉ : w ⟶ y) (h₁ : α ≫ c₁ = G.map c₃ ≫ c₈) (h₂ : c₆.hom ≫ c₉ = P.map c₇ ≫ c₂.hom)
    (h₃ : c₅ ≫ c₉ = G.map c₄.hom ≫ c₈) :
    α ≫ (c₁ ≫ c₂.inv) = G.map (c₃ ≫ c₄.inv) ≫ (c₅ ≫ c₆.inv) ≫ P.map c₇ := by
  have h₂' : c₆.inv ≫ P.map c₇ = c₉ ≫ c₂.inv := by
    rw [Iso.inv_comp_eq, ← Category.assoc, h₂, Category.assoc, Iso.hom_inv_id,
      Category.comp_id]
  have h₃' : G.map c₄.inv ≫ c₅ ≫ c₉ = c₈ := by
    rw [h₃, ← Category.assoc, ← G.map_comp, Iso.inv_hom_id, G.map_id, Category.id_comp]
  rw [← Category.assoc, h₁, G.map_comp]
  simp only [Category.assoc]
  rw [h₂', reassoc_of% h₃']

/-- Naturality of the comparison `T_M` in the object, with every object a variable. -/
theorem comparison_naturality_chase (G : 𝒞' ⥤ 𝒞) (P : 𝒱 ⥤ 𝒞) (Q : 𝒱' ⥤ 𝒞') (L : 𝒱' ⥤ 𝒱)
    {PM' PN' : 𝒞'} {AM AN : 𝒱'} {BM BN : 𝒱} {PM PN : 𝒞} {RM RN : 𝒞}
    (αM : G.obj PM' ⟶ PM) (αN : G.obj PN' ⟶ PN) (vM : PM ⟶ P.obj BM) (vN : PN ⟶ P.obj BN)
    (pM : PM' ≅ Q.obj AM) (pN : PN' ≅ Q.obj AN) (aM : G.obj (Q.obj AM) ⟶ RM)
    (aN : G.obj (Q.obj AN) ⟶ RN) (bM : RM ⟶ P.obj (L.obj AM)) (bN : RN ⟶ P.obj (L.obj AN))
    (rM : L.obj AM ≅ BM) (rN : L.obj AN ≅ BN) (φ : AM ⟶ AN) (μ : RM ⟶ RN)
    (hkM : αM ≫ vM = G.map pM.hom ≫ (aM ≫ bM) ≫ P.map rM.hom)
    (hkN : αN ≫ vN = G.map pN.hom ≫ (aN ≫ bN) ≫ P.map rN.hom)
    (ha : G.map (Q.map φ) ≫ aN = aM ≫ μ) (hb : μ ≫ bN = bM ≫ P.map (L.map φ)) :
    αM ≫ vM ≫ P.map (rM.inv ≫ L.map φ ≫ rN.hom) =
      G.map pM.hom ≫ G.map (Q.map φ) ≫ G.map pN.inv ≫ αN ≫ vN := by
  rw [reassoc_of% hkM, hkN, ← G.map_comp_assoc pN.inv, Iso.inv_hom_id, G.map_id,
    Category.id_comp, Category.assoc, reassoc_of% ha, reassoc_of% hb]
  simp only [← P.map_comp, Iso.hom_inv_id_assoc]

/-- The compatibility with shrinking, with every object a variable. -/
theorem shrink_chase (G : 𝒞' ⥤ 𝒞) {A₀ B PM PN QM QN : 𝒞} {A₀' B' PM' PN' QM' QN' : 𝒞'}
    (eV : B ≅ A₀) (eU : B' ≅ A₀') (zM : B ⟶ PM) (zN : B ⟶ PN) (zM' : B' ⟶ PM')
    (zN' : B' ⟶ PN') (αΔ : G.obj B' ≅ B) (αM : G.obj PM' ⟶ PM) (αN : G.obj PN' ⟶ PN)
    (hzM : αΔ.hom ≫ zM = G.map zM' ≫ αM) (hzN : αΔ.hom ≫ zN = G.map zN' ≫ αN)
    (pM : PM' ≅ QM') (pN : PN' ≅ QN') (vM : PM ⟶ QM) (vN : PN ⟶ QN) (φ' : QM' ⟶ QN')
    (φ : QM ⟶ QN) (hT : αM ≫ vM ≫ φ = G.map pM.hom ≫ G.map φ' ≫ G.map pN.inv ≫ αN ≫ vN)
    (h : (eU.inv ≫ zM' ≫ pM.hom) ≫ φ' = eU.inv ≫ zN' ≫ pN.hom) :
    (eV.inv ≫ zM ≫ vM) ≫ φ = eV.inv ≫ zN ≫ vN := by
  have h' : zM' ≫ pM.hom ≫ φ' = zN' ≫ pN.hom := by
    simpa only [Category.assoc, cancel_epi] using h
  have hzM' : zM = αΔ.inv ≫ G.map zM' ≫ αM := (Iso.eq_inv_comp _).mpr hzM
  have hzN' : zN = αΔ.inv ≫ G.map zN' ≫ αN := (Iso.eq_inv_comp _).mpr hzN
  rw [hzM', hzN']
  simp only [Category.assoc]
  have hG : G.map zM' ≫ G.map pM.hom ≫ G.map φ' ≫ G.map pN.inv = G.map zN' := by
    simp only [← G.map_comp, reassoc_of% h', Iso.hom_inv_id, Category.comp_id]
  rw [hT, reassoc_of% hG]

/-- Naturality of the restriction of `ξ`, with every object a variable. -/
theorem naturality_chase (G : 𝒞' ⥤ 𝒞) {A : 𝒞} {B PM PN : 𝒞'} {Y₁ Y₂ Z₁ Z₂ : 𝒞}
    (e : A ⟶ G.obj B) (ζ : B ⟶ PM) (q : PM ⟶ PN) (aM : G.obj PM ⟶ Y₁) (aN : G.obj PN ⟶ Y₂)
    (k : Y₁ ⟶ Y₂) (bM : Y₁ ⟶ Z₁) (bN : Y₂ ⟶ Z₂) (r : Z₁ ⟶ Z₂)
    (h₁ : G.map q ≫ aN = aM ≫ k) (h₂ : k ≫ bN = bM ≫ r) :
    e ≫ G.map (ζ ≫ q) ≫ (aN ≫ bN) = (e ≫ G.map ζ ≫ (aM ≫ bM)) ≫ r := by
  simp only [G.map_comp, Category.assoc]
  rw [reassoc_of% h₁, h₂]

end Stacks.Duality.RelativeDualizingRestrictLE

namespace AlgebraicGeometry.Scheme.Hom.DiagonalOpen

attribute [local instance 10000] HasDerivedCategory.standard

variable {X S : Scheme.{u}} {f : X ⟶ S} (D : DiagonalOpen f) {U V : X.Opens} (hVU : V ≤ U)

/-- The map `V ×_S V ⟶ U ×_S U` induced by `V ⊆ U`. -/
abbrev pullbackOpensMapOfLE :
    pullback (V.ι ≫ f) (V.ι ≫ f) ⟶ pullback (U.ι ≫ f) (U.ι ≫ f) :=
  pullback.map _ _ _ _ (X.homOfLE hVU) (X.homOfLE hVU) (𝟙 S) (by simp) (by simp)

/-- `V ×_S V ⟶ U ×_S U ⟶ X ×_S X` is the inclusion of `V ×_S V`. -/
theorem pullbackOpensMapOfLE_comp :
    pullbackOpensMapOfLE (f := f) hVU ≫ pullbackOpensMap (f := f) U.ι =
      pullbackOpensMap (f := f) V.ι := by
  ext <;> simp

/-- The map `W_V ⟶ W_U` of restricted diagonal opens induced by `V ⊆ U`. -/
def restrictMapOfLE : (D.restrict V.ι).W ⟶ (D.restrict U.ι).W :=
  pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ pullbackOpensMapOfLE (f := f) hVU)
    (by rw [pullback.condition, Category.assoc, pullbackOpensMapOfLE_comp hVU])

/-- `W_V ⟶ W_U ⟶ W` is the inclusion of `W_V`. -/
@[reassoc]
theorem restrictMapOfLE_restrictInclusion :
    D.restrictMapOfLE hVU ≫ D.restrictInclusion U.ι = D.restrictInclusion V.ι :=
  pullback.lift_fst _ _ _

/-- `W_V ⟶ W_U` lies over `V ⟶ U` along the first projections. -/
@[reassoc]
theorem restrictMapOfLE_proj :
    D.restrictMapOfLE hVU ≫ (D.restrict U.ι).proj = (D.restrict V.ι).proj ≫ X.homOfLE hVU := by
  simp only [restrict, proj, restrictMapOfLE]
  rw [pullback.lift_snd_assoc, Category.assoc]
  exact congrArg (_ ≫ ·) (pullback.lift_fst _ _ _)

/-- `resComp`'s two constituents, read as `pullCompIso`. -/
theorem derivedPullbackCompObj_trans_congrObj_hom {Y Z T : Scheme.{u}} (a : Y ⟶ Z) (b : Z ⟶ T)
    (k : Y ⟶ T) (w : a ≫ b = k) (K : DerivedCategory T.Modules) :
    (Scheme.derivedPullbackCompObj a b K ≪≫ Scheme.derivedPullbackCongrObj w K).hom =
      (pullCompIso a b k w).hom.app K := by
  subst w
  refine Eq.trans ?_ (pullCompIso_hom_app_rfl a b K).symm
  exact Category.comp_id _

omit D in
/-- `resComp` is `pullCompIso` along `V ⟶ U ⟶ X`. -/
theorem resComp_eq_pullCompIso (M : DerivedCategory (OXMod.{u, u} X.toRingedSpace)) :
    resComp hVU M = (pullCompIso (X.homOfLE hVU) U.ι V.ι (X.homOfLE_ι hVU)).app M :=
  Iso.ext (derivedPullbackCompObj_trans_congrObj_hom _ _ _ (X.homOfLE_ι hVU) M)

/-- The composition isomorphisms of derived pullback along `W_V ⟶ W_U ⟶ W`: restricting
`L pr₁^*M|_W` to `W_V` directly or through `W_U` agree, read through
`L pr₁^*(Lj_U^*M)|_{W_U}` and the restriction from `U` to `V`. -/
theorem restrictProjIso_comp_eq (M : DerivedCategory (OXMod.{u, u} X.toRingedSpace)) :
    (pullCompIso (D.restrictMapOfLE hVU) (D.restrictInclusion U.ι) (D.restrictInclusion V.ι)
        (D.restrictMapOfLE_restrictInclusion hVU)).hom.app ((pull D.proj).obj M) ≫
        (D.restrictProjIso V.ι M).hom =
      (pull (D.restrictMapOfLE hVU)).map (D.restrictProjIso U.ι M).hom ≫
        ((pullCompIso (D.restrictMapOfLE hVU) (D.restrict U.ι).proj
            ((D.restrict V.ι).proj ≫ X.homOfLE hVU) (D.restrictMapOfLE_proj hVU)).hom.app
            ((pull U.ι).obj M) ≫
          (pullCompIso (D.restrict V.ι).proj (X.homOfLE hVU) _ rfl).inv.app
            ((pull U.ι).obj M)) ≫
        (pull (D.restrict V.ι).proj).map
          ((pullCompIso (X.homOfLE hVU) U.ι V.ι (X.homOfLE_ι hVU)).app M).hom := by
  have w₁ : ((D.restrict V.ι).proj ≫ X.homOfLE hVU) ≫ U.ι = (D.restrict V.ι).proj ≫ V.ι := by
    rw [Category.assoc, X.homOfLE_ι]
  have w₂ : D.restrictMapOfLE hVU ≫ (D.restrict U.ι).proj ≫ U.ι =
      (D.restrict V.ι).proj ≫ V.ι := by
    rw [← Category.assoc, D.restrictMapOfLE_proj hVU, w₁]
  have h₁ := pullCompIso_assoc (D.restrictMapOfLE hVU) (D.restrictInclusion U.ι) D.proj
    (D.restrictMapOfLE_restrictInclusion hVU) (D.restrictInclusion_proj U.ι)
    (D.restrictInclusion_proj V.ι) w₂ M
  have h₂ := pullCompIso_assoc (D.restrict V.ι).proj (X.homOfLE hVU) U.ι rfl
    (X.homOfLE_ι hVU) w₁ rfl M
  have h₃ := pullCompIso_assoc (D.restrictMapOfLE hVU) (D.restrict U.ι).proj U.ι
    (D.restrictMapOfLE_proj hVU) rfl w₁ w₂ M
  dsimp only [restrictProjIso, Iso.trans_hom, Iso.symm_hom, Iso.app_hom, Iso.app_inv]
  exact Stacks.Duality.RelativeDualizingRestrictLE.comp_cocycle_chase
    (pull (D.restrictMapOfLE hVU)) (pull (D.restrict V.ι).proj)
    ((pullCompIso (D.restrictMapOfLE hVU) (D.restrictInclusion U.ι) (D.restrictInclusion V.ι)
      (D.restrictMapOfLE_restrictInclusion hVU)).hom.app ((pull D.proj).obj M))
    ((pullCompIso (D.restrictInclusion V.ι) D.proj ((D.restrict V.ι).proj ≫ V.ι)
      (D.restrictInclusion_proj V.ι)).hom.app M)
    ((pullCompIso (D.restrict V.ι).proj V.ι _ rfl).app M)
    ((pullCompIso (D.restrictInclusion U.ι) D.proj ((D.restrict U.ι).proj ≫ U.ι)
      (D.restrictInclusion_proj U.ι)).hom.app M)
    ((pullCompIso (D.restrict U.ι).proj U.ι _ rfl).app M)
    ((pullCompIso (D.restrictMapOfLE hVU) ((D.restrict U.ι).proj ≫ U.ι)
      ((D.restrict V.ι).proj ≫ V.ι) w₂).hom.app M)
    ((pullCompIso (D.restrictMapOfLE hVU) (D.restrict U.ι).proj
      ((D.restrict V.ι).proj ≫ X.homOfLE hVU) (D.restrictMapOfLE_proj hVU)).hom.app
        ((pull U.ι).obj M))
    ((pullCompIso (D.restrict V.ι).proj (X.homOfLE hVU) _ rfl).app ((pull U.ι).obj M))
    ((pullCompIso (X.homOfLE hVU) U.ι V.ι (X.homOfLE_ι hVU)).hom.app M)
    ((pullCompIso ((D.restrict V.ι).proj ≫ X.homOfLE hVU) U.ι
      ((D.restrict V.ι).proj ≫ V.ι) w₁).hom.app M) h₁ h₂ h₃

/-- **The restriction of `ζ` to an open `U`**: `restrictXi` at `U.ι`, read in the spelling of
`derivedPullbackProj`. -/
def restrictXiProj (U : X.Opens) (M : DerivedCategory (OXMod.{u, u} X.toRingedSpace))
    (ζ : D.diagonalObject ⟶ D.derivedPullbackProj M) :
    (D.restrict U.ι).diagonalObject ⟶
      (D.restrict U.ι).derivedPullbackProj ((derivedPullback U.ι.toLRSHom.toShHom).obj M) :=
  D.restrictXi U.ι M ζ

/-- **`restrictXiProj` is natural in the object**: restricting `ζ ≫ L pr₁^*φ` is restricting
`ζ` and then applying `L pr₁^*(φ|_U)`. -/
theorem restrictXiProj_comp_derivedPullbackProjMap (U : X.Opens)
    {M N : DerivedCategory (OXMod.{u, u} X.toRingedSpace)}
    (ζ : D.diagonalObject ⟶ D.derivedPullbackProj M) (φ : M ⟶ N) :
    D.restrictXiProj U N (ζ ≫ D.derivedPullbackProjMap φ) =
      D.restrictXiProj U M ζ ≫ (D.restrict U.ι).derivedPullbackProjMap
        ((derivedPullback U.ι.toLRSHom.toShHom).map φ) := by
  have h₁ := (pullCompIso (D.restrictInclusion U.ι) D.proj ((D.restrict U.ι).proj ≫ U.ι)
    (D.restrictInclusion_proj U.ι)).hom.naturality φ
  have h₂ := (pullCompIso (D.restrict U.ι).proj U.ι _ rfl).inv.naturality φ
  have key := Stacks.Duality.RelativeDualizingRestrictLE.naturality_chase
    (pull (D.restrictInclusion U.ι)) (D.restrictDiagonalObjectIso U.ι).inv ζ
    ((pull D.proj).map φ)
    ((pullCompIso (D.restrictInclusion U.ι) D.proj ((D.restrict U.ι).proj ≫ U.ι)
      (D.restrictInclusion_proj U.ι)).hom.app M)
    ((pullCompIso (D.restrictInclusion U.ι) D.proj ((D.restrict U.ι).proj ≫ U.ι)
      (D.restrictInclusion_proj U.ι)).hom.app N)
    ((pull ((D.restrict U.ι).proj ≫ U.ι)).map φ)
    ((pullCompIso (D.restrict U.ι).proj U.ι _ rfl).inv.app M)
    ((pullCompIso (D.restrict U.ι).proj U.ι _ rfl).inv.app N)
    ((pull (D.restrict U.ι).proj).map ((pull U.ι).map φ)) h₁ h₂
  exact key

/-- **`restrictXiProj` is compatible with shrinking the open.** For opens `V ⊆ U` of `X`, if
the restrictions of `ζ_M` and `ζ_N` to `U` are related by `φ : M|_U ⟶ N|_U`, their
restrictions to `V` are related by the restriction of `φ` to `V`. -/
theorem restrictXiProj_comp_derivedPullbackProjMap_of_le
    {M N : DerivedCategory (OXMod.{u, u} X.toRingedSpace)}
    (ζM : D.diagonalObject ⟶ D.derivedPullbackProj M)
    (ζN : D.diagonalObject ⟶ D.derivedPullbackProj N)
    (φ : (derivedPullback U.ι.toLRSHom.toShHom).obj M ⟶
      (derivedPullback U.ι.toLRSHom.toShHom).obj N)
    (h : D.restrictXiProj U M ζM ≫ (D.restrict U.ι).derivedPullbackProjMap φ =
      D.restrictXiProj U N ζN) :
    D.restrictXiProj V M ζM ≫ (D.restrict V.ι).derivedPullbackProjMap
        ((resComp hVU M).inv ≫ (pullbackLE hVU).map φ ≫ (resComp hVU N).hom) =
      D.restrictXiProj V N ζN := by
  have hU : D.restrictXiOf U.ι (D.restrictDiagonalObjectIso U.ι) M ζM ≫
      (pull (D.restrict U.ι).proj).map φ =
        D.restrictXiOf U.ι (D.restrictDiagonalObjectIso U.ι) N ζN := h
  have hz := (pullCompIso (D.restrictMapOfLE hVU) (D.restrictInclusion U.ι)
    (D.restrictInclusion V.ι) (D.restrictMapOfLE_restrictInclusion hVU)).hom.naturality
  have ha := (pullCompIso (D.restrictMapOfLE hVU) (D.restrict U.ι).proj
    ((D.restrict V.ι).proj ≫ X.homOfLE hVU) (D.restrictMapOfLE_proj hVU)).hom.naturality φ
  have hb := (pullCompIso (D.restrict V.ι).proj (X.homOfLE hVU) _ rfl).inv.naturality φ
  have hT := Stacks.Duality.RelativeDualizingRestrictLE.comparison_naturality_chase
    (pull (D.restrictMapOfLE hVU)) (pull (D.restrict V.ι).proj) (pull (D.restrict U.ι).proj)
    (pull (X.homOfLE hVU))
    ((pullCompIso (D.restrictMapOfLE hVU) (D.restrictInclusion U.ι) (D.restrictInclusion V.ι)
      (D.restrictMapOfLE_restrictInclusion hVU)).hom.app ((pull D.proj).obj M))
    ((pullCompIso (D.restrictMapOfLE hVU) (D.restrictInclusion U.ι) (D.restrictInclusion V.ι)
      (D.restrictMapOfLE_restrictInclusion hVU)).hom.app ((pull D.proj).obj N))
    (D.restrictProjIso V.ι M).hom (D.restrictProjIso V.ι N).hom
    (D.restrictProjIso U.ι M) (D.restrictProjIso U.ι N)
    ((pullCompIso (D.restrictMapOfLE hVU) (D.restrict U.ι).proj
      ((D.restrict V.ι).proj ≫ X.homOfLE hVU) (D.restrictMapOfLE_proj hVU)).hom.app
        ((pull U.ι).obj M))
    ((pullCompIso (D.restrictMapOfLE hVU) (D.restrict U.ι).proj
      ((D.restrict V.ι).proj ≫ X.homOfLE hVU) (D.restrictMapOfLE_proj hVU)).hom.app
        ((pull U.ι).obj N))
    ((pullCompIso (D.restrict V.ι).proj (X.homOfLE hVU) _ rfl).inv.app ((pull U.ι).obj M))
    ((pullCompIso (D.restrict V.ι).proj (X.homOfLE hVU) _ rfl).inv.app ((pull U.ι).obj N))
    ((pullCompIso (X.homOfLE hVU) U.ι V.ι (X.homOfLE_ι hVU)).app M)
    ((pullCompIso (X.homOfLE hVU) U.ι V.ι (X.homOfLE_ι hVU)).app N) φ
    ((pull ((D.restrict V.ι).proj ≫ X.homOfLE hVU)).map φ)
    (D.restrictProjIso_comp_eq hVU M) (D.restrictProjIso_comp_eq hVU N) ha hb
  have key := Stacks.Duality.RelativeDualizingRestrictLE.shrink_chase
    (pull (D.restrictMapOfLE hVU)) (D.restrictDiagonalObjectIso V.ι)
    (D.restrictDiagonalObjectIso U.ι)
    ((pull (D.restrictInclusion V.ι)).map ζM) ((pull (D.restrictInclusion V.ι)).map ζN)
    ((pull (D.restrictInclusion U.ι)).map ζM) ((pull (D.restrictInclusion U.ι)).map ζN)
    ((pullCompIso (D.restrictMapOfLE hVU) (D.restrictInclusion U.ι)
      (D.restrictInclusion V.ι) (D.restrictMapOfLE_restrictInclusion hVU)).app
        D.diagonalObject)
    ((pullCompIso (D.restrictMapOfLE hVU) (D.restrictInclusion U.ι) (D.restrictInclusion V.ι)
      (D.restrictMapOfLE_restrictInclusion hVU)).hom.app ((pull D.proj).obj M))
    ((pullCompIso (D.restrictMapOfLE hVU) (D.restrictInclusion U.ι) (D.restrictInclusion V.ι)
      (D.restrictMapOfLE_restrictInclusion hVU)).hom.app ((pull D.proj).obj N))
    (hz ζM).symm (hz ζN).symm (D.restrictProjIso U.ι M) (D.restrictProjIso U.ι N)
    (D.restrictProjIso V.ι M).hom (D.restrictProjIso V.ι N).hom
    ((pull (D.restrict U.ι).proj).map φ) _ hT hU
  rw [resComp_eq_pullCompIso hVU M, resComp_eq_pullCompIso hVU N]
  exact key

end AlgebraicGeometry.Scheme.Hom.DiagonalOpen

namespace AlgebraicGeometry.Scheme.Hom

attribute [local instance 10000] HasDerivedCategory.standard

variable {X S : Scheme.{u}} {f : X ⟶ S} [Flat f] [LocallyOfFinitePresentation f]
  {D : DiagonalOpen f} {K : DerivedCategory (OXMod.{u, u} X.toRingedSpace)}
  {ξ : D.diagonalObject ⟶ D.derivedPullbackProj K}

/-- **The restriction of a relative dualizing complex to an open `U` is a relative dualizing
complex**, with `ξ` restricted by `DiagonalOpen.restrictXiProj`. -/
theorem IsRelativeDualizingComplex.restrictProj
    (hK : IsRelativeDualizingComplex f
      (RingedSpace.canonicalCertifiedDerivedSheafTensoringFamily
        (RingedSpace.inverseImage S.toRingedSpace f.base)) D K ξ)
    (U : X.Opens) :
    IsRelativeDualizingComplex (U.ι ≫ f)
      (RingedSpace.canonicalCertifiedDerivedSheafTensoringFamily
        (RingedSpace.inverseImage S.toRingedSpace (U.ι ≫ f).base)) (D.restrict U.ι)
      ((derivedPullback U.ι.toLRSHom.toShHom).obj K) (D.restrictXiProj U K ξ) :=
  hK.restrict U.ι

end AlgebraicGeometry.Scheme.Hom

end
