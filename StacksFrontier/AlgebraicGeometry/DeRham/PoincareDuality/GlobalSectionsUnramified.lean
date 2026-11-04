module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.RingTheory.Unramified.Field
public import Mathlib.RingTheory.Unramified.Pi
public import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing
public import StacksFrontier.AlgebraicGeometry.Chow.BivariantLemmas.ConnectedComponents
public import StacksFrontier.AlgebraicGeometry.Descent.FpqcDescentProperties.NoetherianNormalDecomposition
public import StacksFrontier.AlgebraicGeometry.Properties.Noetherian
public import StacksFrontier.AlgebraicGeometry.Properties.Normal
public import StacksFrontier.AlgebraicGeometry.ProperSectionsGeom.Separable
public import StacksFrontier.AlgebraicGeometry.Variety.Smooth.GeometricallyRegularNormal
public import StacksFrontier.RingTheory.Smooth.GeometricallyReducedFibres
public import StacksFrontier.Topology.Noetherian.LocallyConnected
public import StacksFrontier.Topology.Noetherian.QuasiCompactLocally
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Global functions on a normal proper scheme over a field

Let `X` be a scheme proper over a field `k` whose local rings are normal domains. Then `X` has
finitely many connected components, each of them open and closed; each component is integral,
because a connected normal Noetherian scheme is irreducible; and the ring of global functions on
an integral scheme proper over `k` is a field finite over `k`. Restriction to the components
therefore presents `Γ(X, 𝒪_X)` as a finite product of finite field extensions of `k`.

When `X` is in addition smooth over `k` those field extensions are separable, so `Γ(X, 𝒪_X)` is
unramified over `k`: the module of relative differentials `Ω_{Γ(X, 𝒪_X)/k}` vanishes, and
therefore every `k`-derivation out of `Γ(X, 𝒪_X)` is zero.

## Main results

* `AlgebraicGeometry.globalSectionsFieldDecomposition_of_isNormal`: a scheme normal and proper
  over a field has a `Stacks.AlgebraicGeometry.ProperSectionsGeom.GlobalSectionsFieldDecomposition`
  — a presentation of its global functions as a finite product of finite field extensions of the
  base field.
* `AlgebraicGeometry.formallyUnramified_globalSections_of_smooth`: the global functions of a
  smooth proper scheme over a field are unramified over that field.

## Implementation notes

The decomposition is indexed by the connected components of `X`, which are open because a
locally Noetherian space is locally connected, and closed because a connected component always
is. Restriction to a family of pairwise disjoint opens covering the space is bijective on
sections: injectivity is the separatedness half of the sheaf axiom, and surjectivity is the
gluing half, the compatibility condition being vacuous because the pairwise intersections are
empty and the sections of a sheaf over the empty open form a terminal object.

That a connected normal Noetherian scheme is irreducible is
`AlgebraicGeometry.irreducibleSpace_of_isNormal_of_connectedSpace`. Properness and local finite
type of each component over the base come from the component being open and closed, which makes
its inclusion a closed immersion and hence proper.

The field and finiteness statements about a component are Mathlib's
`AlgebraicGeometry.isField_of_universallyClosed` and
`AlgebraicGeometry.finite_appTop_of_universallyClosed`, which are about the global sections
`Γ(U, ⊤)` of the component as a scheme in its own right; they are transported to `Γ(X, U)` along
`AlgebraicGeometry.Scheme.Opens.topIso`. The compatibility of that transport with the restriction
map is `AlgebraicGeometry.Scheme.Opens.ι_appTop_comp_topIso_hom`, proved as a term rather than by
`rw`: the intermediate object is `Γ(U, ⊤)` on one side and `Γ(X, U.ι ''ᵁ ⊤)` on the other, which
are definitionally but not syntactically equal, so rewriting cannot type-check its motive.

Normality rather than reducedness is assumed, so this is *not* the reduced-sections half of
Stacks Tag 0BUG and carries no tag: Tag 0BUG asserts the decomposition for a *reduced* proper
scheme, and that is a strictly weaker hypothesis. What is proved here is what the smooth case
needs, since a scheme smooth over a field is regular and hence normal.

## References

* [Stacks Project, Tag 0BUG](https://stacks.math.columbia.edu/tag/0BUG)
* [Stacks Project, Tag 0357](https://stacks.math.columbia.edu/tag/0357)
* [Stacks Project, Tag 056T](https://stacks.math.columbia.edu/tag/056T)
* [Stacks Project, Tag 090W](https://stacks.math.columbia.edu/tag/090W)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Stacks.AlgebraicGeometry.ProperSectionsGeom (GlobalSectionsFieldDecomposition)
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry

/-! ### Sections over a pairwise disjoint open cover -/

/-- Sections over `U ⊆ X` of the structure sheaf of `X`, read through the identification of `U`
with the global sections of `U` as a scheme in its own right, are computed by the restriction
map. The composite is the same morphism as the restriction `Γ(X, ⊤) ⟶ Γ(X, U)`, and that is
proved as a term: the intermediate object is `Γ(U, ⊤)` on the left and `Γ(X, U.ι ''ᵁ ⊤)` on the
right, which are definitionally but not syntactically equal, so a rewrite cannot type-check its
motive. -/
theorem Scheme.Opens.ι_appTop_comp_topIso_hom {X : Scheme.{u}} (U : X.Opens) :
    U.ι.appTop ≫ U.topIso.hom = X.presheaf.map (homOfLE le_top).op :=
  (X.presheaf.map_comp (homOfLE (x := U.ι ''ᵁ ⊤) le_top).op
      (eqToIso U.ι_image_top.symm).op.hom).symm.trans
    (congrArg X.presheaf.map (Subsingleton.elim _ _))

/-- **Restriction to a pairwise disjoint open cover is bijective on sections.** Injectivity is
the separatedness half of the sheaf axiom. Surjectivity is the gluing half: the compatibility
condition is vacuous, because the pairwise intersections are empty and the sections of a sheaf
over the empty open form a terminal object, hence a subsingleton. -/
theorem bijective_restrict_of_pairwise_disjoint {X : Scheme.{u}} {ι : Type u} (U : ι → X.Opens)
    (hcover : (⊤ : X.Opens) ≤ ⨆ i, U i)
    (hdisjoint : Pairwise fun i j => Disjoint (U i) (U j)) :
    Function.Bijective
      (fun s : Γ(X, ⊤) => fun i => X.presheaf.map (homOfLE (le_top (a := U i))).op s) := by
  have hcompatible (sf : ∀ i, Γ(X, U i)) : TopCat.Presheaf.IsCompatible X.presheaf U sf := by
    intro i j
    by_cases hij : i = j
    · subst hij; rfl
    · have hterminal := X.sheaf.isTerminalOfEqEmpty (U := U i ⊓ U j) (hdisjoint hij).eq_bot
      have huniq : Unique ((CategoryTheory.forget CommRingCat).obj
          (X.sheaf.obj.obj (op (U i ⊓ U j)))) :=
        (Types.isTerminalEquivUnique _).1
          (IsTerminal.isTerminalObj (CategoryTheory.forget CommRingCat) _ hterminal)
      exact (huniq.uniq _).trans (huniq.uniq _).symm
  refine ⟨fun s t hst => ?_, fun sf => ?_⟩
  · exact X.sheaf.eq_of_locally_eq' U ⊤ (fun i => homOfLE le_top) hcover s t fun i =>
      congrFun hst i
  · obtain ⟨s, hs, -⟩ :=
      X.sheaf.existsUnique_gluing' U ⊤ (fun i => homOfLE le_top) hcover sf (hcompatible sf)
    exact ⟨s, funext hs⟩

/-! ### The connected components of a normal proper scheme -/

section Components

variable (k : Type u) [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsProper f]

include f

/-- A scheme proper over a field is Noetherian: it is locally of finite type over a Noetherian
base, hence locally Noetherian, and universally closed, hence quasi-compact. -/
private theorem isNoetherian_of_isProper_over_field : IsNoetherian X where
  __ := LocallyOfFiniteType.isLocallyNoetherian f
  __ := compactSpace_of_universallyClosed f

/-- The connected components of a scheme proper over a field are open: the space is locally
Noetherian, hence locally connected. -/
@[ega "I 6.1.9" "special case",
  sga "1 IX 5.1" "special case",
  sga "3 VIA 2.3" "special case",
  sga "3 X 5.11.0" "special case"]
private theorem locallyConnectedSpace_of_isProper_over_field : LocallyConnectedSpace X :=
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  (isLocallyNoetherianSpace_of_isLocallyNoetherian X).locallyConnectedSpace X

/-- A scheme proper over a field has only finitely many connected components, its space being
Noetherian. -/
@[ega "IV 4.4.1" "special case", sga "3 X 5.11.0" "special case", sga "4 XII 5.6" "partial"]
private theorem finite_connectedComponents_of_isProper_over_field :
    Finite (_root_.ConnectedComponents X) :=
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have : CompactSpace X := compactSpace_of_universallyClosed f
  have : NoetherianSpace X := noetherianSpace_of_isLocallyNoetherianSpace X
    (isLocallyNoetherianSpace_of_isLocallyNoetherian X)
  NoetherianSpace.finite_connectedComponents X

variable [LocallyConnectedSpace X]

/-- The inclusion of a connected component of a scheme proper over a field is a closed
immersion, the component being open and closed, so the component is again proper over the
base. -/
private theorem isProper_connectedComponentOpens_ι_comp (c : _root_.ConnectedComponents X) :
    IsProper ((X.connectedComponentOpens c).ι ≫ f) :=
  have : IsClosedImmersion (X.connectedComponentOpens c).ι :=
    ⟨⟨(X.connectedComponentOpens c).ι.isOpenEmbedding.isEmbedding, by
      rw [(X.connectedComponentOpens c).range_ι]
      exact X.isClosed_connectedComponentOpens c⟩⟩
  inferInstance

variable [IsNormal X]

/-- A connected component of a normal scheme proper over a field is integral: it is normal, it is
Noetherian, and it is connected, hence irreducible. -/
private theorem isIntegral_connectedComponentOpens (c : _root_.ConnectedComponents X) :
    IsIntegral (X.connectedComponentOpens c).toScheme := by
  have := isNoetherian_of_isProper_over_field k f
  have : IsReduced X := isReduced_of_isNormal X
  have : CompactSpace (X.connectedComponentOpens c).toScheme :=
    isCompact_iff_compactSpace.mp (X.isClosed_connectedComponentOpens c).isCompact
  have : IsNoetherian (X.connectedComponentOpens c).toScheme := ⟨⟩
  have : IsNormal (X.connectedComponentOpens c).toScheme :=
    isNormal_open (X.connectedComponentOpens c)
  have : ConnectedSpace (X.connectedComponentOpens c).toScheme := by
    obtain ⟨x, hx⟩ := ConnectedComponents.surjective_coe c
    have hset : ((X.connectedComponentOpens c : X.Opens) : Set X) = connectedComponent x := by
      rw [X.coe_connectedComponentOpens, ← hx]
      exact connectedComponents_preimage_singleton
    exact isConnected_iff_connectedSpace.mp (hset ▸ isConnected_connectedComponent)
  have := irreducibleSpace_of_isNormal_of_connectedSpace
    (X.connectedComponentOpens c).toScheme inferInstance
  exact isIntegral_of_irreducibleSpace_of_isReduced _

/-- The ring of functions on a connected component of a normal scheme proper over a field is a
field: the component is integral and universally closed over the base. -/
private theorem isField_sections_connectedComponentOpens (c : _root_.ConnectedComponents X) :
    IsField Γ(X, X.connectedComponentOpens c) := by
  have := isIntegral_connectedComponentOpens k f c
  have := isProper_connectedComponentOpens_ι_comp k f c
  exact ((X.connectedComponentOpens c).topIso.commRingCatIsoToRingEquiv.toMulEquiv.isField_congr).mp
    (isField_of_universallyClosed k ((X.connectedComponentOpens c).ι ≫ f))

omit [IsProper f] [IsNormal X] in
/-- The structure map `k ⟶ Γ(X, U)` of a connected component, as the restriction along `U ⊆ X`
of the structure map of `X`, factors as the structure map of `U` as a scheme over `k` followed by
`AlgebraicGeometry.Scheme.Opens.topIso`. -/
private theorem structureMap_connectedComponentOpens_eq (c : _root_.ConnectedComponents X) :
    ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop) ≫
        X.presheaf.map (homOfLE (le_top (a := X.connectedComponentOpens c))).op =
      ((Scheme.ΓSpecIso (.of k)).inv ≫
        ((X.connectedComponentOpens c).ι ≫ f).appTop) ≫
          (X.connectedComponentOpens c).topIso.hom := by
  rw [← Scheme.Opens.ι_appTop_comp_topIso_hom (X.connectedComponentOpens c),
    Scheme.Hom.comp_appTop]
  simp only [Category.assoc]

/-- The map `k ⟶ Γ(X, U)` giving the functions on a connected component their `k`-algebra
structure is finite: it is the one Mathlib's finiteness statement for an integral universally
closed scheme over a field describes, read through
`AlgebraicGeometry.Scheme.Opens.topIso`. -/
private theorem finite_structureMap_connectedComponentOpens (c : _root_.ConnectedComponents X) :
    ((((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop) ≫
      X.presheaf.map
        (homOfLE (le_top (a := X.connectedComponentOpens c))).op).hom).Finite := by
  have := isIntegral_connectedComponentOpens k f c
  have := isProper_connectedComponentOpens_ι_comp k f c
  rw [structureMap_connectedComponentOpens_eq k f c]
  refine RingHom.Finite.comp ?_ ?_
  · exact RingHom.Finite.of_surjective _
      (ConcreteCategory.bijective_of_isIso (X.connectedComponentOpens c).topIso.hom).2
  · exact (finite_appTop_of_universallyClosed k ((X.connectedComponentOpens c).ι ≫ f)).comp
      (RingHom.Finite.of_surjective ((Scheme.ΓSpecIso (.of k)).inv.hom) (fun x =>
        ⟨(Scheme.ΓSpecIso (.of k)).hom.hom x, by simp⟩))

end Components

/-! ### The decomposition of the global functions -/

/-- **The ring of global functions on a normal scheme proper over a field is a finite product of
finite field extensions of that field.** The factors are the rings of functions on the connected
components, each of which is integral and proper over the base.

This is the shape in which Stacks Tag 0BUG hands the decomposition on. It carries no tag: Tag
0BUG asserts it for a *reduced* proper scheme, and normality is a strictly stronger hypothesis. -/
theorem globalSectionsFieldDecomposition_of_isNormal (k : Type u) [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [IsProper f] [IsNormal X] :
    Nonempty (GlobalSectionsFieldDecomposition k X f) := by
  classical
  have : LocallyConnectedSpace X := locallyConnectedSpace_of_isProper_over_field k f
  have : Finite (_root_.ConnectedComponents X) :=
    finite_connectedComponents_of_isProper_over_field k f
  have : Fintype (_root_.ConnectedComponents X) := Fintype.ofFinite _
  let U (c : _root_.ConnectedComponents X) : X.Opens := X.connectedComponentOpens c
  let : Algebra k Γ(X, ⊤) := ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop).hom.toAlgebra
  let (c : _root_.ConnectedComponents X) : Algebra k Γ(X, U c) :=
    (((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop) ≫
      X.presheaf.map (homOfLE le_top).op).hom.toAlgebra
  let restrictAll : Γ(X, ⊤) →ₐ[k] (∀ c, Γ(X, U c)) :=
    { toFun := fun s c => X.presheaf.map (homOfLE le_top).op s
      map_one' := by ext; simp
      map_mul' := fun a b => by ext; simp
      map_zero' := by ext; simp
      map_add' := fun a b => by ext; simp
      commutes' := fun r => by ext c; rfl }
  have hbij : Function.Bijective restrictAll :=
    bijective_restrict_of_pairwise_disjoint U (le_of_eq X.iSup_connectedComponentOpens.symm)
      fun _ _ h => X.disjoint_connectedComponentOpens h
  let idx : Fin (Fintype.card (_root_.ConnectedComponents X)) ≃ _root_.ConnectedComponents X :=
    (Fintype.equivFin (_root_.ConnectedComponents X)).symm
  refine ⟨⟨Fintype.card (_root_.ConnectedComponents X),
    fun i => CommAlgCat.of k Γ(X, U (idx i)), fun i => ?_, fun i => ?_, ?_⟩⟩
  · exact isField_sections_connectedComponentOpens k f (idx i)
  · exact finite_structureMap_connectedComponentOpens k f (idx i)
  · exact (AlgEquiv.ofBijective restrictAll hbij).trans
      (AlgEquiv.piCongrLeft' k (fun c => Γ(X, U c)) idx.symm)

/-- **The global functions of a smooth proper scheme over a field are unramified over that
field**, so every `k`-derivation out of `Γ(X, 𝒪_X)` vanishes.

A scheme smooth over `k` is regular, hence normal, so its global functions are a finite product
of finite field extensions of `k`; and it is geometrically reduced over `k`, so each of those
extensions is separable (Stacks Tag 0BUG), hence unramified. -/
theorem formallyUnramified_globalSections_of_smooth (k : Type u) [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [Smooth f] [IsProper f] :
    letI : Algebra k Γ(X, ⊤) := ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop).hom.toAlgebra
    Algebra.FormallyUnramified k Γ(X, ⊤) := by
  have : IsNormal X := isNormal_of_isRegular X (isRegular_of_smooth_over_field f)
  have : GeometricallyReduced f := geometricallyReduced_of_smooth f
  let : Algebra k Γ(X, ⊤) := ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop).hom.toAlgebra
  obtain ⟨D⟩ := globalSectionsFieldDecomposition_of_isNormal k f
  have hpi : Algebra.FormallyUnramified k (∀ i, D.factor i) := by
    rw [Algebra.FormallyUnramified.pi_iff]
    intro i
    let : Field (D.factor i) := (D.factorIsField i).toField
    have : Module.Finite k (D.factor i) := D.factorModuleFinite i
    have : Algebra.EssFiniteType k (D.factor i) := inferInstance
    exact (Algebra.FormallyUnramified.iff_isSeparable k (D.factor i)).2
      (GlobalSectionsFieldDecomposition.factor_isSeparable k f D i)
  exact (Algebra.FormallyUnramified.iff_of_equiv D.algEquiv).mpr hpi

end AlgebraicGeometry

end
