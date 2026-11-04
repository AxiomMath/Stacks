module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Crystalline.CrystalConnectionOpenSections
public import StacksFrontier.AlgebraicGeometry.Crystalline.FirstOrderIdealKernelCrystal
public import StacksFrontier.AlgebraicGeometry.Crystalline.SecondOrderIdealTensorMono

/-!
# Integrability of the canonical connection of [Stacks, Lemma 60.15.1, Tag 07J6]

Fix a global crystalline situation `(p, (S, I, γ), X)` of [Stacks, Tag 07MF], let `F` be a
sheaf crystal in `𝒪_{X/S}`-modules on the big crystalline site and let
`(U, T, δ)` be an object of `CRIS(X/S)`.  Write `Ω = Ω_{T/S,δ}` and `Ω² = Ω²_{T/S,δ}`.

[Stacks, Tag 07J6] puts its connection

`∇ : F_T ⟶ F_T ⊗_{𝒪_T} Ω`

on the **sheaf** tensor product, and reads its integrability as an identity of sections of the
subsheaf `F_T ⊗ Ω²` of `q₂^* F`.  This module builds exactly that: the connection and its
degree-one extension of [Stacks, Section 60.15, Tag 07J5] on the sections over every open of `T`,
and the vanishing of their composite.

## The construction

Three facts from the library are used, and nothing else.

1. `Crystalline.GlobalCrystallineSituation.isIso_firstOrderKernelComparison_of_isSheafCrystal`:
   the canonical morphism `F_T ⊗_{𝒪_T} Ω ⟶ ker(i^* : p₀_* F_{T'} ⟶ F_T)` is an isomorphism.  The
   connection `∇(s) = p₁^* s - p₀^* s` of
   `Crystalline.GlobalCrystallineSituation.crystalConnectionOpen` takes values in that kernel, by
   `Crystalline.GlobalCrystallineSituation.crystalConnectionOpen_restrict_ι`, so the inverse
   isomorphism reads it inside `F_T ⊗_{𝒪_T} Ω`.  That is
   `Crystalline.GlobalCrystallineSituation.crystalConnectionSheaf`, and
   `Crystalline.GlobalCrystallineSituation.firstOrderTensorInclusion_crystalConnectionSheaf`
   says that the canonical morphism carries it back to `p₁^* s - p₀^* s`: the connection built
   here is the tag's own one, read where the tag reads it.
2. The curvature identity
   `Crystalline.GlobalCrystallineSituation.crystalConnectionOpen_cocycle`, which is the
   commutative triangle `q₁₂^* c ∘ q₀₁^* c = q₀₂^* c` of the source's integrability argument.  It
   holds for every sheaf of `𝒪_{X/S}`-modules and every open.
3. `Crystalline.GlobalCrystallineSituation.isSplitMono_secondOrderTensorComparison`: the
   degree-two canonical morphism `F_T ⊗_{𝒪_T} Ω² ⟶ q₀_* F_{T''}` is a split monomorphism.  Its
   retraction turns the source's computation inside `q₀_* F_{T''}` into a section of
   `F_T ⊗_{𝒪_T} Ω²`, which is precisely the step the source describes as reading the outcome "as
   a section of the subsheaf `F_T ⊗ Ω²_{T/S,δ}` of `q₂^* F`".

The source's computation itself is
`Crystalline.GlobalCrystallineSituation.secondOrderCurvatureSheaf`, the alternating sum

`q₀₁^* (z ·) + q₁₂^* (z ·) - q₀₂^* (z ·)`

of the three restrictions to `(U, T'', δ'')` of a section `z` of `F_T ⊗ Ω` read inside
`p₀_* F_{T'}`; the source's two displayed expressions are its two halves.  The degree-one
extension `∇ : F_T ⊗ Ω ⟶ F_T ⊗ Ω²` of §07J5 is that alternating sum read in `F_T ⊗ Ω²` through
the retraction, which is what the source's computation shows it to be.  Integrability is then the
curvature identity: on `z = ∇(s)` the alternating sum is the alternating sum of the three
restrictions of `p₁^* s - p₀^* s`, which vanishes.

## Main definitions

* `Crystalline.GlobalCrystallineSituation.firstOrderTensorInclusion` — the canonical morphism
  `F_T ⊗_{𝒪_T} Ω ⟶ p₀_* F_{T'}`, the identification of [Stacks, Tag 07J6] followed by the
  inclusion of the kernel.  No hypothesis.
* `Crystalline.GlobalCrystallineSituation.crystalConnectionSheaf` — **the connection of
  [Stacks, Tag 07J6] on the sections over an open, read inside `F_T ⊗_{𝒪_T} Ω`.**
* `Crystalline.GlobalCrystallineSituation.secondOrderCurvatureSheaf` — the source's alternating
  sum, a map from the sections of `F_T ⊗ Ω` over an open to the sections of `F` over the
  restriction of `(U, T'', δ'')` to that open.  No hypothesis.
* `Crystalline.GlobalCrystallineSituation.secondOrderTensorRetraction` — the retraction of the
  degree-two canonical morphism.
* `Crystalline.GlobalCrystallineSituation.extendedConnectionSheaf` — **the degree-one extension
  of the connection of [Stacks, Section 60.15, Tag 07J5]**, `F_T ⊗ Ω ⟶ F_T ⊗ Ω²`, on the
  sections over an open.

## Main results

* `Crystalline.GlobalCrystallineSituation.firstOrderTensorInclusion_crystalConnectionSheaf` —
  the canonical morphism carries the connection back to `p₁^* s - p₀^* s`.
* `Crystalline.GlobalCrystallineSituation.crystalConnectionSheaf_naturality` — the connection
  commutes with restriction to a smaller open, so it is one morphism of sheaves of abelian
  groups `F_T ⟶ F_T ⊗_{𝒪_T} Ω`.
* `Crystalline.GlobalCrystallineSituation.injective_firstOrderTensorInclusion` — the canonical
  morphism is injective on the sections over every open, so the previous identity determines the
  connection.
* `Crystalline.GlobalCrystallineSituation.secondOrderCurvatureSheaf_crystalConnectionSheaf` —
  the source's alternating sum vanishes on the values of the connection.  This is the curvature
  identity, and it is where the hypotheses on `F` are not used at all.
* `Crystalline.GlobalCrystallineSituation.extendedConnectionSheaf_naturality` — the degree-one
  extension commutes with restriction to a smaller open, so it too is one morphism of sheaves of
  abelian groups.
* `Crystalline.GlobalCrystallineSituation.extendedConnectionSheaf_eq_of_comparison` — the
  degree-one extension of a section is the unique section of `F_T ⊗ Ω²` whose image under the
  degree-two canonical morphism is the alternating sum, which is the source's own identification
  of `∇²`.
* `Crystalline.GlobalCrystallineSituation.crystalConnectionSheaf_isIntegrable` —
  **[Stacks, Lemma 60.15.1, Tag 07J6]: the canonical connection of a crystal is integrable**, as
  an identity of sections over every open of the ambient scheme of every object.

## Status of [Stacks, Tag 07J6]

[Stacks, Tag 07J6] itself — a crystal on the small site `Cris(X/S)` has a canonical integrable
connection — is formalized, with no quasi-coherence hypothesis, in
`StacksFrontier/AlgebraicGeometry/Crystalline/SmallSite/CrystalIntegrableConnectionCris.lean`,
in the namespace `Crystalline.GlobalCrystallineSituation.SmallSite`: the connection
`crystalConnectionCris : F ⟶ F ⊗ Ω_{X/S}`, a morphism of abelian sheaves on `Cris(X/S)`, and the
theorems `crystalConnectionCris_isConnection` and `crystalConnectionCris_isIntegrable`.  This
module is about the big site `CRIS(X/S)` and carries no attribute for that tag.

## References

* [Stacks Project, Tag 07J6](https://stacks.math.columbia.edu/tag/07J6)
* [Stacks Project, Tag 07J5](https://stacks.math.columbia.edu/tag/07J5)
* [Stacks Project, Tag 07J3](https://stacks.math.columbia.edu/tag/07J3)
* [Stacks Project, Tag 07J2](https://stacks.math.columbia.edu/tag/07J2)
* [Stacks Project, Tag 07MF](https://stacks.math.columbia.edu/tag/07MF)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace
  MonoidalCategory

universe u v₁ u₁ t a

noncomputable section

namespace Stacks.SheafOfModules

/-! ### Additivity of a morphism of sheaves of modules on local sections

A morphism of sheaves of modules is additive on the sections over each object of the site. -/

section Sections

variable {C : Type u₁} [Category.{v₁} C] {J : CategoryTheory.GrothendieckTopology C}
  {R : CategoryTheory.Sheaf J RingCat.{t}} {X Y : SheafOfModules.{a} R}

/-- A morphism of sheaves of modules preserves addition of sections over `U`. -/
theorem val_app_add (φ : X ⟶ Y) (U : Cᵒᵖ) (x y : X.val.obj U) :
    φ.val.app U (x + y) = φ.val.app U x + φ.val.app U y :=
  map_add (φ.val.app U).hom x y

/-- A morphism of sheaves of modules sends the zero section over `U` to zero. -/
theorem val_app_zero (φ : X ⟶ Y) (U : Cᵒᵖ) :
    φ.val.app U (0 : X.val.obj U) = 0 :=
  map_zero (φ.val.app U).hom

/-- **A morphism of sheaves of modules on the sections over one object of the site, as an additive
map.** -/
def valAppHom (φ : X ⟶ Y) (U : Cᵒᵖ) : X.val.obj U →+ Y.val.obj U :=
  (φ.val.app U).hom.toAddMonoidHom

/-- The additive map `valAppHom φ U` sends a section `x` over `U` to `φ.val.app U x`. -/
@[simp]
theorem valAppHom_apply (φ : X ⟶ Y) (U : Cᵒᵖ) (x : X.val.obj U) :
    valAppHom φ U x = φ.val.app U x := rfl

/-- Applying `f` then `g` to a section over `U` is applying `k` when `f ≫ g = k`. -/
private theorem val_app_comp_apply {Z : SheafOfModules.{a} R} {f : X ⟶ Y} {g : Y ⟶ Z}
    {k : X ⟶ Z} (h : f ≫ g = k) (U : Cᵒᵖ) (x : X.val.obj U) :
    g.val.app U (f.val.app U x) = k.val.app U x :=
  h ▸ rfl

end Sections

end Stacks.SheafOfModules

namespace Crystalline

attribute [local instance] monoidalCategorySchemeModules

namespace GlobalCrystallineSituation

variable {S : GlobalCrystallineSituation.{u}}
  (M : SheafOfModules.{u} (crystallineStructureSheaf S)) (A : Thickening S)

/-! ### The canonical morphism `F_T ⊗ Ω ⟶ p₀_* F_{T'}` -/

/-- `p₀_* F_{T'}`, the direct image along the first projection of [Stacks, Tag 07J2] of the
restriction of `F` to the ambient scheme of the first-order universal thickening. -/
abbrev firstOrderAmbientPushforward : A.thickening.target.scheme.Modules :=
  (Scheme.Modules.pushforward (firstOrderThickeningSiteP₀ S A).targetHom.hom).obj
    (Thickening.ambientSchemeModule M (firstOrderThickeningObject S A))

/-- `q₀_* F_{T''}`, the direct image along the first projection of [Stacks, Tag 07J3]. -/
abbrev secondOrderAmbientPushforward : A.thickening.target.scheme.Modules :=
  (Scheme.Modules.pushforward (secondOrderThickeningSiteQ₀ S A).targetHom.hom).obj
    (Thickening.ambientSchemeModule M (secondOrderThickeningObject S A))

/-- **The canonical morphism `F_T ⊗_{𝒪_T} Ω_{T/S,δ} ⟶ p₀_* F_{T'}`**: the identification
`Crystalline.GlobalCrystallineSituation.firstOrderKernelComparison` of [Stacks, Tag 07J6]
followed by the inclusion of the kernel of restriction along the diagonal.  No hypothesis. -/
def firstOrderTensorInclusion :
    firstOrderThickeningTensorDifferentials A.thickening.target S.S.scheme A.toBase.hom
        (Thickening.ambientSchemeModule M A) ⟶
      firstOrderAmbientPushforward M A :=
  firstOrderKernelComparison M A ≫ kernel.ι (firstOrderAmbientProjMap₀ M A)

/-- **The canonical morphism is injective on the sections over every open** as soon as the
identification of [Stacks, Tag 07J6] is an isomorphism: the inclusion of the kernel is split by
`Crystalline.GlobalCrystallineSituation.firstOrderAmbientRetraction`, so it is injective on
sections, and an isomorphism is. -/
theorem injective_firstOrderTensorInclusion (hM : IsSheafCrystal M)
    (W : A.thickening.target.scheme.Opens) :
    Function.Injective
      (Stacks.SheafOfModules.valAppHom (firstOrderTensorInclusion M A) (op W)) := by
  have := isIso_firstOrderKernelComparison_of_isSheafCrystal M A hM
  intro z z' hz
  have hsplit : ∀ y : (firstOrderAmbientKernel M A).val.obj (op W),
      (firstOrderAmbientRetraction M A).val.app (op W)
        ((kernel.ι (firstOrderAmbientProjMap₀ M A)).val.app (op W) y) = y := fun y ↦
    Stacks.SheafOfModules.val_app_comp_apply (firstOrderAmbientSplitting M A).f_r (op W) y
  have h1 : ∀ w : (firstOrderThickeningTensorDifferentials A.thickening.target S.S.scheme
        A.toBase.hom (Thickening.ambientSchemeModule M A)).val.obj (op W),
      (inv (firstOrderKernelComparison M A)).val.app (op W)
        ((firstOrderKernelComparison M A).val.app (op W) w) = w := fun w ↦
    Stacks.SheafOfModules.val_app_comp_apply (IsIso.hom_inv_id (firstOrderKernelComparison M A))
      (op W) w
  have e : ∀ x : (firstOrderThickeningTensorDifferentials A.thickening.target S.S.scheme
        A.toBase.hom (Thickening.ambientSchemeModule M A)).val.obj (op W),
      (firstOrderAmbientRetraction M A).val.app (op W)
          ((firstOrderTensorInclusion M A).val.app (op W) x) =
        (firstOrderKernelComparison M A).val.app (op W) x := fun x ↦
    hsplit ((firstOrderKernelComparison M A).val.app (op W) x)
  have hcomp : (firstOrderKernelComparison M A).val.app (op W) z =
      (firstOrderKernelComparison M A).val.app (op W) z' :=
    ((e z).symm.trans
      (congrArg (fun y ↦ (firstOrderAmbientRetraction M A).val.app (op W) y) hz)).trans (e z')
  exact ((h1 z).symm.trans
    (congrArg (fun y ↦ (inv (firstOrderKernelComparison M A)).val.app (op W) y) hcomp)).trans
      (h1 z')

/-! ### The connection on the sections over an open, read inside `F_T ⊗ Ω` -/

/-- **The canonical connection of [Stacks, Lemma 60.15.1, Tag 07J6] on the sections over an open,
read inside `F_T ⊗_{𝒪_T} Ω_{T/S,δ}`.**  The value `∇(s) = p₁^* s - p₀^* s` is a section of
`p₀_* F_{T'}` killed by restriction along the diagonal, hence a section of the kernel of `i^*`,
and the identification of [Stacks, Tag 07J6] carries that kernel isomorphically onto
`F_T ⊗_{𝒪_T} Ω_{T/S,δ}`.

It is a map of sections over each open, additive but not `𝒪_T`-linear — the Leibniz rule
`∇(f s) = f ∇(s) + s ⊗ d f` of the source is exactly its failure to be linear — and it is
characterised by
`Crystalline.GlobalCrystallineSituation.firstOrderTensorInclusion_crystalConnectionSheaf`
together with
`Crystalline.GlobalCrystallineSituation.injective_firstOrderTensorInclusion`. -/
def crystalConnectionSheaf (hM : IsSheafCrystal M)
    (W : A.thickening.target.scheme.Opens) :
    M.val.obj (op (A.restrictOpen W)) →+
      (firstOrderThickeningTensorDifferentials A.thickening.target S.S.scheme A.toBase.hom
        (Thickening.ambientSchemeModule M A)).val.obj (op W) :=
  (Stacks.SheafOfModules.valAppHom
      (firstOrderKernelIsoOfIsSheafCrystal M A hM).inv (op W)).comp
    ((Stacks.SheafOfModules.valAppHom (firstOrderAmbientRetraction M A) (op W)).comp
      (crystalConnectionOpen A W M))

/-- The connection `crystalConnectionSheaf M A hM W` sends `s` to the image of
`crystalConnectionOpen A W M s` under the retraction onto the kernel of restriction along the
diagonal, followed by the inverse of the identification of that kernel with
`F_T ⊗_{𝒪_T} Ω_{T/S,δ}`. -/
theorem crystalConnectionSheaf_apply (hM : IsSheafCrystal M)
    (W : A.thickening.target.scheme.Opens) (s : M.val.obj (op (A.restrictOpen W))) :
    crystalConnectionSheaf M A hM W s =
      (firstOrderKernelIsoOfIsSheafCrystal M A hM).inv.val.app (op W)
        ((firstOrderAmbientRetraction M A).val.app (op W) (crystalConnectionOpen A W M s)) := rfl

/-- **The canonical morphism carries the connection back to `p₁^* s - p₀^* s`.**  So the section
of `F_T ⊗_{𝒪_T} Ω_{T/S,δ}` built by
`Crystalline.GlobalCrystallineSituation.crystalConnectionSheaf` is the connection of
[Stacks, Tag 07J6] and not some other section: its image under the identification the tag uses is
the tag's own `∇(s)`.

The proof is the splitting of `p₀_* F_{T'} = ker(i^*) ⊞ F_T`: the retraction onto the kernel is
`1 - p₀^* ∘ i^*`, and `i^* ∇(s) = 0` by
`Crystalline.GlobalCrystallineSituation.crystalConnectionOpen_restrict_ι`. -/
theorem firstOrderTensorInclusion_crystalConnectionSheaf (hM : IsSheafCrystal M)
    (W : A.thickening.target.scheme.Opens)
    (s : M.val.obj (op (A.restrictOpen W))) :
    (firstOrderTensorInclusion M A).val.app (op W)
        (crystalConnectionSheaf M A hM W s) =
      crystalConnectionOpen A W M s := by
  have hhom : ∀ y : (firstOrderAmbientKernel M A).val.obj (op W),
      (firstOrderKernelComparison M A).val.app (op W)
        ((firstOrderKernelIsoOfIsSheafCrystal M A hM).inv.val.app (op W) y) = y := fun y ↦
    Stacks.SheafOfModules.val_app_comp_apply
      (firstOrderKernelIsoOfIsSheafCrystal M A hM).inv_hom_id (op W) y
  have hsub : ∀ y : (firstOrderAmbientPushforward M A).val.obj (op W),
      (𝟙 (firstOrderAmbientPushforward M A) -
          firstOrderAmbientProjMap₀ M A ≫ firstOrderAmbientInclMap M A).val.app (op W) y =
        y - (firstOrderAmbientInclMap M A).val.app (op W)
          ((firstOrderAmbientProjMap₀ M A).val.app (op W) y) := fun _ ↦ rfl
  have hret : ∀ y : (firstOrderAmbientPushforward M A).val.obj (op W),
      (kernel.ι (firstOrderAmbientProjMap₀ M A)).val.app (op W)
          ((firstOrderAmbientRetraction M A).val.app (op W) y) =
        (𝟙 (firstOrderAmbientPushforward M A) -
          firstOrderAmbientProjMap₀ M A ≫ firstOrderAmbientInclMap M A).val.app (op W) y := fun y ↦
    Stacks.SheafOfModules.val_app_comp_apply (firstOrderAmbientRetraction_ι M A) (op W) y
  have hι : (firstOrderAmbientProjMap₀ M A).val.app (op W) (crystalConnectionOpen A W M s) = 0 :=
    crystalConnectionOpen_restrict_ι A W M s
  have h3 : (firstOrderAmbientInclMap M A).val.app (op W)
      ((firstOrderAmbientProjMap₀ M A).val.app (op W) (crystalConnectionOpen A W M s)) = 0 :=
    (congrArg (fun y ↦ (firstOrderAmbientInclMap M A).val.app (op W) y) hι).trans
      (Stacks.SheafOfModules.val_app_zero (firstOrderAmbientInclMap M A) (op W))
  have e1 : (firstOrderTensorInclusion M A).val.app (op W)
        (crystalConnectionSheaf M A hM W s) =
      (kernel.ι (firstOrderAmbientProjMap₀ M A)).val.app (op W)
        ((firstOrderKernelComparison M A).val.app (op W)
          ((firstOrderKernelIsoOfIsSheafCrystal M A hM).inv.val.app (op W)
            ((firstOrderAmbientRetraction M A).val.app (op W)
              (crystalConnectionOpen A W M s)))) := rfl
  refine e1.trans ?_
  refine (congrArg (fun y ↦ (kernel.ι (firstOrderAmbientProjMap₀ M A)).val.app (op W) y)
    (hhom ((firstOrderAmbientRetraction M A).val.app (op W)
      (crystalConnectionOpen A W M s)))).trans ?_
  exact ((hret (crystalConnectionOpen A W M s)).trans
    (hsub (crystalConnectionOpen A W M s))).trans (sub_eq_self.mpr h3)

/-- **The connection commutes with restriction to a smaller open.**  Both the retraction onto the
kernel and the identification of [Stacks, Tag 07J6] are morphisms of sheaves of `𝒪_T`-modules,
hence compatible with restriction, and the connection on the sections over an open is by
`Crystalline.GlobalCrystallineSituation.crystalConnectionOpen_naturality`.

So the maps over the opens of `T` are the components of one morphism of sheaves of abelian groups

`∇ : F_T ⟶ F_T ⊗_{𝒪_T} Ω_{T/S,δ}`,

which is the connection of [Stacks, Lemma 60.15.1, Tag 07J6]. -/
theorem crystalConnectionSheaf_naturality (hM : IsSheafCrystal M)
    {W W' : A.thickening.target.scheme.Opens} (h : W' ≤ W)
    (s : M.val.obj (op (A.restrictOpen W))) :
    (firstOrderThickeningTensorDifferentials A.thickening.target S.S.scheme A.toBase.hom
          (Thickening.ambientSchemeModule M A)).val.map (homOfLE h).op
        (crystalConnectionSheaf M A hM W s) =
      crystalConnectionSheaf M A hM W' (moduleSiteRestrict M (A.restrictOpenLE h) s) := by
  have hr := PresheafOfModules.naturality_apply (firstOrderAmbientRetraction M A).val
    (homOfLE h).op (crystalConnectionOpen A W M s)
  have hi := PresheafOfModules.naturality_apply
    (firstOrderKernelIsoOfIsSheafCrystal M A hM).inv.val (homOfLE h).op
    ((firstOrderAmbientRetraction M A).val.app (op W) (crystalConnectionOpen A W M s))
  have hn := crystalConnectionOpen_naturality A M h s
  exact hi.symm.trans (congrArg
    (fun z ↦ (firstOrderKernelIsoOfIsSheafCrystal M A hM).inv.val.app (op W') z)
    (hr.symm.trans (congrArg
      (fun z ↦ (firstOrderAmbientRetraction M A).val.app (op W') z) hn)))

/-! ### The source's alternating sum on the second-order thickening -/

/-- **The alternating sum of [Stacks, Lemma 60.15.1, Tag 07J6]**: for a section `z` of
`F_T ⊗_{𝒪_T} Ω_{T/S,δ}` over an open `W`, read inside `p₀_* F_{T'}` by the canonical morphism,
the combination

`q₀₁^* z + q₁₂^* z - q₀₂^* z`

of its three restrictions to the second-order universal thickening of [Stacks, Tag 07J3].  The
source's two displayed expressions `q₁₂^* c ∘ q₀₁^* c (q₀^* s)` and `q₀₂^* c (q₀^* s)` differ by
this combination at `z = ∇(s)`, and the source identifies it with `∇²(s)` read inside
`F_T ⊗ Ω²_{T/S,δ}`.  No hypothesis. -/
def secondOrderCurvatureSheaf (W : A.thickening.target.scheme.Opens) :
    (firstOrderThickeningTensorDifferentials A.thickening.target S.S.scheme A.toBase.hom
        (Thickening.ambientSchemeModule M A)).val.obj (op W) →+
      M.val.obj (op ((secondOrderThickeningObject S A).restrictOpen W)) :=
  ((moduleSiteRestrict M (secondOrderRestrictQ₀₁ A W)).toAddMonoidHom.comp
        (Stacks.SheafOfModules.valAppHom (firstOrderTensorInclusion M A) (op W)) +
      (moduleSiteRestrict M (secondOrderRestrictQ₁₂ A W)).toAddMonoidHom.comp
        (Stacks.SheafOfModules.valAppHom (firstOrderTensorInclusion M A) (op W))) -
    (moduleSiteRestrict M (secondOrderRestrictQ₀₂ A W)).toAddMonoidHom.comp
      (Stacks.SheafOfModules.valAppHom (firstOrderTensorInclusion M A) (op W))

/-- The value of `secondOrderCurvatureSheaf M A W` at `z` is `q₀₁^* z + q₁₂^* z - q₀₂^* z`,
with `z` read inside `p₀_* F_{T'}` by `firstOrderTensorInclusion M A`. -/
theorem secondOrderCurvatureSheaf_apply (W : A.thickening.target.scheme.Opens)
    (z : (firstOrderThickeningTensorDifferentials A.thickening.target S.S.scheme A.toBase.hom
      (Thickening.ambientSchemeModule M A)).val.obj (op W)) :
    secondOrderCurvatureSheaf M A W z =
      (moduleSiteRestrict M (secondOrderRestrictQ₀₁ A W)
            ((firstOrderTensorInclusion M A).val.app (op W) z) :
          M.val.obj (op ((secondOrderThickeningObject S A).restrictOpen W))) +
        moduleSiteRestrict M (secondOrderRestrictQ₁₂ A W)
          ((firstOrderTensorInclusion M A).val.app (op W) z) -
        moduleSiteRestrict M (secondOrderRestrictQ₀₂ A W)
          ((firstOrderTensorInclusion M A).val.app (op W) z) := rfl

/-- **The alternating sum commutes with restriction to a smaller open.**  The canonical morphism
is a morphism of sheaves of `𝒪_T`-modules and the restrictions of the three morphisms of
[Stacks, Tag 07J3] over `W` and over `W'` are compatible, by
`Crystalline.GlobalCrystallineSituation.Thickening.restrictOpenLE_restrictOpenMap`. -/
theorem secondOrderCurvatureSheaf_naturality {W W' : A.thickening.target.scheme.Opens}
    (h : W' ≤ W)
    (z : (firstOrderThickeningTensorDifferentials A.thickening.target S.S.scheme A.toBase.hom
      (Thickening.ambientSchemeModule M A)).val.obj (op W)) :
    moduleSiteRestrict M ((secondOrderThickeningObject S A).restrictOpenLE h)
        (secondOrderCurvatureSheaf M A W z) =
      secondOrderCurvatureSheaf M A W'
        ((firstOrderThickeningTensorDifferentials A.thickening.target S.S.scheme A.toBase.hom
          (Thickening.ambientSchemeModule M A)).val.map (homOfLE h).op z) := by
  have eδ : moduleSiteRestrict M ((firstOrderThickeningObject S A).restrictOpenLE h)
        ((firstOrderTensorInclusion M A).val.app (op W) z) =
      (firstOrderTensorInclusion M A).val.app (op W')
        ((firstOrderThickeningTensorDifferentials A.thickening.target S.S.scheme A.toBase.hom
          (Thickening.ambientSchemeModule M A)).val.map (homOfLE h).op z) :=
    (PresheafOfModules.naturality_apply (firstOrderTensorInclusion M A).val
      (homOfLE h).op z).symm
  have e₀₁ : (secondOrderThickeningObject S A).restrictOpenLE h ≫ secondOrderRestrictQ₀₁ A W =
      secondOrderRestrictQ₀₁ A W' ≫ (firstOrderThickeningObject S A).restrictOpenLE h :=
    Thickening.restrictOpenLE_restrictOpenMap (secondOrderThickeningSiteQ₀₁ S A) h
  have e₁₂ : (secondOrderThickeningObject S A).restrictOpenLE h ≫ secondOrderRestrictQ₁₂ A W =
      secondOrderRestrictQ₁₂ A W' ≫ (firstOrderThickeningObject S A).restrictOpenLE h :=
    Thickening.restrictOpenLE_restrictOpenMap (secondOrderThickeningSiteQ₁₂ S A) h
  have e₀₂ : (secondOrderThickeningObject S A).restrictOpenLE h ≫ secondOrderRestrictQ₀₂ A W =
      secondOrderRestrictQ₀₂ A W' ≫ (firstOrderThickeningObject S A).restrictOpenLE h :=
    Thickening.restrictOpenLE_restrictOpenMap (secondOrderThickeningSiteQ₀₂ S A) h
  have hL := secondOrderCurvatureSheaf_apply M A W z
  have hR := secondOrderCurvatureSheaf_apply M A W'
    ((firstOrderThickeningTensorDifferentials A.thickening.target S.S.scheme A.toBase.hom
      (Thickening.ambientSchemeModule M A)).val.map (homOfLE h).op z)
  have key : ∀ (q : (secondOrderThickeningObject S A).restrictOpen W ⟶
        (firstOrderThickeningObject S A).restrictOpen W)
      (q' : (secondOrderThickeningObject S A).restrictOpen W' ⟶
        (firstOrderThickeningObject S A).restrictOpen W'),
      (secondOrderThickeningObject S A).restrictOpenLE h ≫ q =
          q' ≫ (firstOrderThickeningObject S A).restrictOpenLE h →
        ∀ x : M.val.obj (op ((firstOrderThickeningObject S A).restrictOpen W)),
          moduleSiteRestrict M ((secondOrderThickeningObject S A).restrictOpenLE h)
              (moduleSiteRestrict M q x) =
            moduleSiteRestrict M q'
              (moduleSiteRestrict M
                ((firstOrderThickeningObject S A).restrictOpenLE h) x) := by
    intro q q' e x
    rw [moduleSiteRestrict_comp, moduleSiteRestrict_comp, e]
  have main : ∀ y : M.val.obj (op ((firstOrderThickeningObject S A).restrictOpen W)),
      moduleSiteRestrict M ((secondOrderThickeningObject S A).restrictOpenLE h)
          ((moduleSiteRestrict M (secondOrderRestrictQ₀₁ A W) y :
                M.val.obj (op ((secondOrderThickeningObject S A).restrictOpen W))) +
              moduleSiteRestrict M (secondOrderRestrictQ₁₂ A W) y -
            moduleSiteRestrict M (secondOrderRestrictQ₀₂ A W) y) =
        (moduleSiteRestrict M (secondOrderRestrictQ₀₁ A W')
              (moduleSiteRestrict M ((firstOrderThickeningObject S A).restrictOpenLE h) y) :
              M.val.obj (op ((secondOrderThickeningObject S A).restrictOpen W'))) +
            moduleSiteRestrict M (secondOrderRestrictQ₁₂ A W')
              (moduleSiteRestrict M ((firstOrderThickeningObject S A).restrictOpenLE h) y) -
          moduleSiteRestrict M (secondOrderRestrictQ₀₂ A W')
            (moduleSiteRestrict M ((firstOrderThickeningObject S A).restrictOpenLE h) y) := by
    intro y
    rw [map_sub, map_add, key _ _ e₀₁ y, key _ _ e₁₂ y, key _ _ e₀₂ y]
  refine (congrArg (fun w ↦ moduleSiteRestrict M
    ((secondOrderThickeningObject S A).restrictOpenLE h) w) hL).trans ?_
  refine (main ((firstOrderTensorInclusion M A).val.app (op W) z)).trans ?_
  refine Eq.trans (congrArg (fun v ↦
    (moduleSiteRestrict M (secondOrderRestrictQ₀₁ A W') v :
          M.val.obj (op ((secondOrderThickeningObject S A).restrictOpen W'))) +
        moduleSiteRestrict M (secondOrderRestrictQ₁₂ A W') v -
      moduleSiteRestrict M (secondOrderRestrictQ₀₂ A W') v) eδ) ?_
  exact hR.symm

/-- **The alternating sum vanishes on the values of the connection.**  This is the curvature
identity `Crystalline.GlobalCrystallineSituation.crystalConnectionOpen_cocycle`: the canonical
morphism carries `∇(s)` to `p₁^* s - p₀^* s`, whose three restrictions to the second-order
universal thickening are `q₁^* s - q₀^* s`, `q₂^* s - q₁^* s` and `q₂^* s - q₀^* s`.

In the source this is the commutativity of the triangle
`q₁₂^* c ∘ q₀₁^* c = q₀₂^* c`, which holds "because `F` is a sheaf"; here it holds for every
sheaf of `𝒪_{X/S}`-modules, the crystal hypothesis entering only through the identification that
gives the connection its target. -/
theorem secondOrderCurvatureSheaf_crystalConnectionSheaf (hM : IsSheafCrystal M)
    (W : A.thickening.target.scheme.Opens)
    (s : M.val.obj (op (A.restrictOpen W))) :
    secondOrderCurvatureSheaf M A W (crystalConnectionSheaf M A hM W s) = 0 := by
  rw [secondOrderCurvatureSheaf_apply,
    firstOrderTensorInclusion_crystalConnectionSheaf M A hM W s, sub_eq_zero]
  exact crystalConnectionOpen_cocycle A W M s

/-! ### The degree-one extension of the connection -/

/-- **The retraction of the degree-two canonical morphism `F_T ⊗_{𝒪_T} Ω² ⟶ q₀_* F_{T''}`**, for
a sheaf crystal.  It exists because that morphism is a split
monomorphism, by
`Crystalline.GlobalCrystallineSituation.isSplitMono_secondOrderTensorComparison`: the top summand
`Ω²_{T/S,δ}` of `𝒪_{T''} = 𝒪_T ⊕ Ω ⊕ Ω ⊕ Ω²` of [Stacks, Tag 07J3] is retracted by the top
coordinate, and the two remaining steps of the chain are isomorphisms.

This is the morphism through which [Stacks, Tag 07J6] reads the outcome of its integrability
computation "as a section of the subsheaf `F_T ⊗ Ω²_{T/S,δ}` of `q₂^* F`". -/
def secondOrderTensorRetraction (hM : IsSheafCrystal M) :
    secondOrderAmbientPushforward M A ⟶
      secondOrderThickeningTensorSecondExterior A.thickening.target S.S.scheme A.toBase.hom
        (Thickening.ambientSchemeModule M A) :=
  haveI := isSplitMono_secondOrderTensorComparison M A hM
  retraction (secondOrderTensorComparison M A)

/-- **The degree-two canonical morphism followed by its retraction is the identity.** -/
theorem secondOrderTensorComparison_comp_retraction (hM : IsSheafCrystal M) :
    secondOrderTensorComparison M A ≫ secondOrderTensorRetraction M A hM =
      𝟙 (secondOrderThickeningTensorSecondExterior A.thickening.target S.S.scheme A.toBase.hom
        (Thickening.ambientSchemeModule M A)) :=
  have := isSplitMono_secondOrderTensorComparison M A hM
  IsSplitMono.id (secondOrderTensorComparison M A)

/-- **The degree-one extension of the connection, of [Stacks, Section 60.15, Tag 07J5]**, on the
sections over an open:

`∇ : F_T ⊗_{𝒪_T} Ω_{T/S,δ} ⟶ F_T ⊗_{𝒪_T} Ω²_{T/S,δ}`.

It is the source's alternating sum
`Crystalline.GlobalCrystallineSituation.secondOrderCurvatureSheaf` read inside `F_T ⊗ Ω²` through
the retraction of the degree-two canonical morphism — which is what the source's computation
shows the rule `∇(s ⊗ ω) = ∇(s) ∧ ω + s ⊗ d ω` of §07J5 to be: for `z = ∑ s_i ⊗ ω_i` the
alternating sum is `∑ q₂^* s_i · d ω_i - ∑ q₁₂^* ∇(s_i) · q₀₁^* ω_i`, and the two formulae of
[Stacks, Tag 07J3] identify those two terms with `∑ s_i ⊗ d ω_i` and `∑ ∇(s_i) ∧ ω_i` read
through the top summand.

Like the connection itself it is additive and not `𝒪_T`-linear. -/
def extendedConnectionSheaf (hM : IsSheafCrystal M)
    (W : A.thickening.target.scheme.Opens) :
    (firstOrderThickeningTensorDifferentials A.thickening.target S.S.scheme A.toBase.hom
        (Thickening.ambientSchemeModule M A)).val.obj (op W) →+
      (secondOrderThickeningTensorSecondExterior A.thickening.target S.S.scheme A.toBase.hom
        (Thickening.ambientSchemeModule M A)).val.obj (op W) :=
  (Stacks.SheafOfModules.valAppHom (secondOrderTensorRetraction M A hM) (op W)).comp
    (secondOrderCurvatureSheaf M A W)

/-- **The degree-one extension is the source's alternating sum read inside `F_T ⊗ Ω²`.**  If a
section `w` of `F_T ⊗_{𝒪_T} Ω²_{T/S,δ}` over an open has the alternating sum of `z` as its image
under the degree-two canonical morphism, then `w` is the degree-one extension of `z`.

This is what [Stacks, Lemma 60.15.1, Tag 07J6] does with the outcome of its computation: having
found the difference of its two displayed expressions, it reads that difference "as a section of
the subsheaf `F_T ⊗ Ω²_{T/S,δ}` of `q₂^* F`", and this says that
`Crystalline.GlobalCrystallineSituation.extendedConnectionSheaf` is that reading — the retraction
inverts the degree-two canonical morphism wherever the morphism reaches. -/
theorem extendedConnectionSheaf_eq_of_comparison (hM : IsSheafCrystal M)
    (W : A.thickening.target.scheme.Opens)
    (z : (firstOrderThickeningTensorDifferentials A.thickening.target S.S.scheme A.toBase.hom
      (Thickening.ambientSchemeModule M A)).val.obj (op W))
    (w : (secondOrderThickeningTensorSecondExterior A.thickening.target S.S.scheme A.toBase.hom
      (Thickening.ambientSchemeModule M A)).val.obj (op W))
    (h : (secondOrderTensorComparison M A).val.app (op W) w = secondOrderCurvatureSheaf M A W z) :
    extendedConnectionSheaf M A hM W z = w := by
  have hid : ∀ y : (secondOrderThickeningTensorSecondExterior A.thickening.target S.S.scheme
        A.toBase.hom (Thickening.ambientSchemeModule M A)).val.obj (op W),
      (secondOrderTensorRetraction M A hM).val.app (op W)
        ((secondOrderTensorComparison M A).val.app (op W) y) = y := fun y ↦
    Stacks.SheafOfModules.val_app_comp_apply
      (secondOrderTensorComparison_comp_retraction M A hM) (op W) y
  have e : extendedConnectionSheaf M A hM W z =
      (secondOrderTensorRetraction M A hM).val.app (op W)
        (secondOrderCurvatureSheaf M A W z) := rfl
  exact (e.trans (congrArg
    (fun y ↦ (secondOrderTensorRetraction M A hM).val.app (op W) y) h.symm)).trans (hid w)

/-- **The degree-one extension commutes with restriction to a smaller open**, so it too is one
morphism of sheaves of abelian groups `F_T ⊗_{𝒪_T} Ω ⟶ F_T ⊗_{𝒪_T} Ω²`. -/
theorem extendedConnectionSheaf_naturality (hM : IsSheafCrystal M)
    {W W' : A.thickening.target.scheme.Opens} (h : W' ≤ W)
    (z : (firstOrderThickeningTensorDifferentials A.thickening.target S.S.scheme A.toBase.hom
      (Thickening.ambientSchemeModule M A)).val.obj (op W)) :
    (secondOrderThickeningTensorSecondExterior A.thickening.target S.S.scheme A.toBase.hom
          (Thickening.ambientSchemeModule M A)).val.map (homOfLE h).op
        (extendedConnectionSheaf M A hM W z) =
      extendedConnectionSheaf M A hM W'
        ((firstOrderThickeningTensorDifferentials A.thickening.target S.S.scheme A.toBase.hom
          (Thickening.ambientSchemeModule M A)).val.map (homOfLE h).op z) := by
  have hρ := PresheafOfModules.naturality_apply (secondOrderTensorRetraction M A hM).val
    (homOfLE h).op (secondOrderCurvatureSheaf M A W z)
  exact hρ.symm.trans (congrArg
    (fun y ↦ (secondOrderTensorRetraction M A hM).val.app (op W') y)
    (secondOrderCurvatureSheaf_naturality M A h z))

/-- **Stacks Project, Lemma 60.15.1, Tag 07J6: the canonical connection of a crystal in
`𝒪_{X/S}`-modules is integrable.**  For a sheaf crystal `F` on the big
crystalline site, every object `(U, T, δ)` of `CRIS(X/S)`, every open `W` of `T` and every
section `s` of `F_T` over `W`, the composite of the connection

`∇ : F_T ⟶ F_T ⊗_{𝒪_T} Ω_{T/S,δ}`

of `Crystalline.GlobalCrystallineSituation.crystalConnectionSheaf` with its own degree-one
extension of [Stacks, Section 60.15, Tag 07J5] vanishes.

The extension is the source's alternating sum read inside `F_T ⊗ Ω²` through the retraction of
the degree-two canonical morphism, and on the values of the connection that alternating sum is
zero by the curvature identity
`Crystalline.GlobalCrystallineSituation.secondOrderCurvatureSheaf_crystalConnectionSheaf`.  That
is the source's argument: the two displayed expressions of its proof agree, and their difference
is `∇²(s)` read in the subsheaf `F_T ⊗ Ω²_{T/S,δ}` of `q₂^* F`. -/
theorem crystalConnectionSheaf_isIntegrable (hM : IsSheafCrystal M)
    (W : A.thickening.target.scheme.Opens)
    (s : M.val.obj (op (A.restrictOpen W))) :
    extendedConnectionSheaf M A hM W (crystalConnectionSheaf M A hM W s) = 0 := by
  have h : secondOrderCurvatureSheaf M A W (crystalConnectionSheaf M A hM W s) = 0 :=
    secondOrderCurvatureSheaf_crystalConnectionSheaf M A hM W s
  have e : extendedConnectionSheaf M A hM W (crystalConnectionSheaf M A hM W s) =
      Stacks.SheafOfModules.valAppHom (secondOrderTensorRetraction M A hM) (op W)
        (secondOrderCurvatureSheaf M A W (crystalConnectionSheaf M A hM W s)) := rfl
  exact (e.trans (congrArg
    (fun y ↦ Stacks.SheafOfModules.valAppHom (secondOrderTensorRetraction M A hM) (op W) y)
    h)).trans (map_zero _)

end GlobalCrystallineSituation

end Crystalline

end

end
