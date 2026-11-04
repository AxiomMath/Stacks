module

public import StacksFrontier.AlgebraicGeometry.RelativeDifferentialStalk.Sheafify
public import StacksFrontier.CategoryTheory.Sites.Modules.ConormalSequence

/-!
# The stalk of the conormal sheaf

Let `φ : A ⟶ B` be a locally surjective morphism of sheaves of commutative rings on a topological
space `X`, let `I` be its kernel and let `x` be a point of `X`. The stalk at `x` of the conormal
sheaf `I/I²` is the conormal module `Iₓ/Iₓ²` of the kernel `Iₓ` of the induced map `Aₓ → Bₓ` on
stalks.

Sheafification does not change stalks, so the stalk of `I/I²` is the stalk of the presheaf
`U ↦ I(U)/I(U)²`, that is, the filtered colimit of the conormal modules of the sections of the
kernel over the open neighbourhoods of `x`; the content of the statement is that forming `I/I²`
commutes with that colimit, which in turn comes from the exactness of filtered colimits.

## Main definitions

* `Stacks.Sites.Conormal.stalkKernelIdeal`: the kernel `Iₓ` of the map `Aₓ → Bₓ` on stalks.
* `Stacks.Sites.Conormal.conormalPresheafOverSource`: the presheaf `U ↦ I(U)/I(U)²`, regarded as
  a presheaf of `A`-modules.
* `Stacks.Sites.Conormal.germCotangentMap`: the map `I(U)/I(U)² → Iₓ/Iₓ²` sending the class of a
  section of the kernel to the class of its germ.
* `Stacks.Sites.Conormal.conormalStalkHom`: the induced comparison map from the stalk of
  `U ↦ I(U)/I(U)²` to `Iₓ/Iₓ²`.
* `Stacks.Sites.Conormal.conormalPresheafStalkLinearEquiv`: the comparison map as a linear
  equivalence over the stalk of `A`.
* `Stacks.Sites.Conormal.conormalSheafStalkLinearEquiv`: the identification
  `(I/I²)ₓ ≅ Iₓ/Iₓ²`.
* `Stacks.Sites.Conormal.stalkQuotientRingEquiv`: the identification `Aₓ/Iₓ ≅ Bₓ`, which reads
  the stalk of the conormal sheaf as a module over the stalk of `B`.

## Main results

* `Stacks.Sites.Conormal.exists_germ_eq_of_mem_stalkKernelIdeal`: every element of `Iₓ` is the
  germ of a section of the kernel, and
  `Stacks.Sites.Conormal.exists_germ_eq_of_mem_stalkKernelIdeal_sq`: every element of `Iₓ²` is
  the germ of a section of `I(U)²`. These two are the exactness of filtered colimits in the form
  the comparison needs.
* `Stacks.Sites.Conormal.conormalStalkHom_injective` and
  `Stacks.Sites.Conormal.conormalStalkHom_surjective`: the comparison map is bijective.
* `Stacks.Sites.Conormal.conormalSheafStalkLinearEquiv_germ_toAssociatedModule` and
  `Stacks.Sites.Conormal.conormalSheafStalkLinearEquiv_germ_conormalClass`: the identification
  carries the germ of the conormal class of a section `f` of the kernel to the class of the germ
  of `f`. This pins the identification down.
* `Stacks.Sites.Conormal.stalkMap_surjective`: a locally surjective morphism of presheaves of
  commutative rings is surjective on stalks.

## Implementation notes

The conormal presheaf is a presheaf of modules over the image presheaf `U ↦ A(U)/I(U)`, whose
stalk is `Aₓ/Iₓ` but not by definition. To avoid identifying the two rings, every module
structure below is restricted along `A ⟶ A/I`, so that the comparison is linear over the stalk
of `A` itself; the target `Iₓ/Iₓ²` is an `Aₓ`-module for the same reason. Restriction of scalars
does not change the underlying presheaf of abelian groups, so the stalk being compared is
unchanged.

The passage from the conormal presheaf to the conormal sheaf is a single morphism of presheaves
of `A`-modules: the universe lift followed by the unit of sheafification. On underlying presheaves
of abelian groups the first is an isomorphism and the second is the unit of sheafification of
presheaves of abelian groups, which the stalk functor inverts.

Local surjectivity of `φ` is used only through
`Stacks.Sites.Conormal.stalkMap_surjective`, for the identification of `Bₓ` with `Aₓ/Iₓ`; the
comparison of stalks itself holds for an arbitrary morphism of presheaves of commutative rings,
and is proved at that generality.

Membership statements such as `a ∈ kernelIdeal φ (op U)` and the germ equations relating them are
stated with the bundled ring homomorphisms `(A.germ U x hx).hom` rather than with the concrete
category coercion, because the conormal module of a section is a subquotient and rewriting under
the coercion forces unfolding of the module structures.

## References

* [Stacks Project, Tag 08TL](https://stacks.math.columbia.edu/tag/08TL)
* [Stacks Project, Tag 08TM](https://stacks.math.columbia.edu/tag/08TM)
* [Stacks Project, Tag 08TS](https://stacks.math.columbia.edu/tag/08TS)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

universe u

noncomputable section

namespace Stacks.Sites.Conormal

/-! ### The kernel of the map on stalks -/

section Presheaf

variable {X : TopCat.{u}} {A B : X.Presheaf CommRingCat.{u}} (φ : A ⟶ B) (x : X)

/-- The kernel of the ring homomorphism induced by `φ` on the stalks at `x`. -/
abbrev stalkKernelIdeal : Ideal (ToType (A.stalk x)) :=
  RingHom.ker ((TopCat.Presheaf.stalkFunctor CommRingCat.{u} x).map φ).hom

/-- The germ at `x` of a section of the kernel of `φ` lies in the kernel of the map on stalks. -/
theorem kernelIdeal_le_comap_germ (U : Opens X) (hx : x ∈ U) :
    kernelIdeal φ (op U) ≤ (stalkKernelIdeal φ x).comap (A.germ U x hx).hom := by
  intro a ha
  have h := TopCat.Presheaf.stalkFunctor_map_germ_apply U x hx φ a
  show ((TopCat.Presheaf.stalkFunctor CommRingCat.{u} x).map φ).hom
    ((A.germ U x hx).hom a) = 0
  refine h.trans ?_
  rw [show φ.app (op U) a = 0 from ha]
  exact map_zero (B.germ U x hx).hom

/-- The quotient map onto the image presheaf, as a morphism of presheaves of rings. -/
abbrev toQuotientRingHom : A ⋙ forget₂ CommRingCat RingCat ⟶
    quotientPresheaf φ ⋙ forget₂ CommRingCat RingCat :=
  Functor.whiskerRight (toQuotient φ) (forget₂ CommRingCat RingCat)

/-- The presheaf `U ↦ I(U)/I(U)²`, regarded as a presheaf of modules over `A` by restriction of
scalars along `A ⟶ A/I`. -/
def conormalPresheafOverSource : PresheafOfModules.{u} (A ⋙ forget₂ CommRingCat RingCat) :=
  (PresheafOfModules.restrictScalars (toQuotientRingHom φ)).obj (conormalPresheaf φ)

/-! ### The comparison map on sections -/

/-- The map `I(U)/I(U)² → Iₓ/Iₓ²` induced by taking germs at `x`, for an open neighbourhood `U`
of `x`. -/
abbrev germCotangentMap (U : Opens X) (hx : x ∈ U) :
    (kernelIdeal φ (op U)).Cotangent →ₛₗ[Ideal.quotientMap (stalkKernelIdeal φ x)
      (A.germ U x hx).hom (kernelIdeal_le_comap_germ φ x U hx)]
      (stalkKernelIdeal φ x).Cotangent :=
  cotangentMap _ _ (A.germ U x hx).hom (kernelIdeal_le_comap_germ φ x U hx)

/-- The comparison map sends the conormal class of a section of the kernel to the conormal class
of its germ. -/
theorem germCotangentMap_toCotangent (U : Opens X) (hx : x ∈ U) (a : kernelIdeal φ (op U)) :
    germCotangentMap φ x U hx ((kernelIdeal φ (op U)).toCotangent a) =
      (stalkKernelIdeal φ x).toCotangent
        ⟨(A.germ U x hx).hom a, kernelIdeal_le_comap_germ φ x U hx a.2⟩ := rfl

/-- The comparison map on sections is compatible with restriction to a smaller neighbourhood
of `x`. -/
theorem germCotangentMap_map {U V : Opens X} (i : V ⟶ U) (hV : x ∈ V)
    (c : (conormalPresheafOverSource φ).obj (op U)) :
    germCotangentMap φ x V hV ((conormalPresheafOverSource φ).map i.op c) =
      germCotangentMap φ x U (i.le hV) c := by
  obtain ⟨a, rfl⟩ := (kernelIdeal φ (op U)).toCotangent_surjective c
  show (stalkKernelIdeal φ x).toCotangent ⟨(A.germ V x hV).hom ((A.map i.op).hom a), _⟩ =
    (stalkKernelIdeal φ x).toCotangent ⟨(A.germ U x (i.le hV)).hom a, _⟩
  congr 1
  ext
  exact TopCat.Presheaf.germ_res_apply A i x hV (a : A.obj (op U))

/-- The comparison map on sections is semilinear over the germ map of `A`. -/
theorem germCotangentMap_smul (U : Opens X) (hx : x ∈ U) (r : A.obj (op U))
    (c : (conormalPresheafOverSource φ).obj (op U)) :
    germCotangentMap φ x U hx (r • c) = (A.germ U x hx).hom r • germCotangentMap φ x U hx c :=
  map_smulₛₗ (germCotangentMap φ x U hx) (Ideal.Quotient.mk _ r) c

/-- The conormal module `Iₓ/Iₓ²` of the kernel of the map on stalks, as a cocone over the diagram
of the conormal modules of the sections of `I` near `x`. -/
def conormalStalkCocone :
    Cocone ((OpenNhds.inclusion x).op ⋙ (conormalPresheafOverSource φ).presheaf) where
  pt := AddCommGrpCat.of (stalkKernelIdeal φ x).Cotangent
  ι :=
    { app := fun V => AddCommGrpCat.ofHom
        (AddMonoidHom.mk' (germCotangentMap φ x V.unop.1 V.unop.2) (map_add _))
      naturality := by
        intro V W f
        ext c
        exact germCotangentMap_map φ x ((OpenNhds.inclusion x).map f.unop) W.unop.2 c }

/-- The comparison homomorphism from the stalk at `x` of the presheaf `U ↦ I(U)/I(U)²` to the
conormal module `Iₓ/Iₓ²` of the kernel of the map on stalks. -/
def conormalStalkHom :
    ToType (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u})
        (conormalPresheafOverSource φ).presheaf x) →+ (stalkKernelIdeal φ x).Cotangent :=
  (colimit.desc _ (conormalStalkCocone φ x)).hom

/-- The comparison map sends the germ of a section of `U ↦ I(U)/I(U)²` to its image under the
comparison map on sections. -/
theorem conormalStalkHom_germ (U : Opens X) (hx : x ∈ U)
    (c : (conormalPresheafOverSource φ).obj (op U)) :
    conormalStalkHom φ x (TopCat.Presheaf.germ (C := AddCommGrpCat.{u})
        (conormalPresheafOverSource φ).presheaf U x hx c) = germCotangentMap φ x U hx c :=
  ConcreteCategory.congr_hom
    (colimit.ι_desc (conormalStalkCocone φ x) (op (⟨U, hx⟩ : OpenNhds x))) c

/-! ### Germs of sections of the kernel -/

/-- **Every element of the kernel of the map on stalks is the germ of a section of the kernel.**
This is the exactness of filtered colimits. -/
theorem exists_germ_eq_of_mem_stalkKernelIdeal (y : ToType (A.stalk x))
    (hy : y ∈ stalkKernelIdeal φ x) :
    ∃ (U : Opens X) (hx : x ∈ U) (a : A.obj (op U)), a ∈ kernelIdeal φ (op U) ∧
      (A.germ U x hx).hom a = y := by
  obtain ⟨U, hU, a, rfl⟩ := A.exists_germ_eq y
  have h0 : (B.germ U x hU).hom (φ.app (op U) a) = 0 :=
    (TopCat.Presheaf.stalkFunctor_map_germ_apply U x hU φ a).symm.trans hy
  obtain ⟨W, hW, iU, iU', hWe⟩ := B.germ_eq x hU hU (φ.app (op U) a) 0
    (h0.trans (map_zero (B.germ U x hU).hom).symm)
  refine ⟨W, hW, (A.map iU.op).hom a, ?_, ?_⟩
  · show φ.app (op W) ((A.map iU.op).hom a) = 0
    refine (φ.naturality_apply iU.op a).trans ?_
    exact hWe.trans (map_zero (B.map iU'.op).hom)
  · exact TopCat.Presheaf.germ_res_apply A iU x hW a

/-- Restriction to a smaller open set carries the square of the kernel ideal into the square of
the kernel ideal. -/
theorem map_mem_kernelIdeal_sq {U V : Opens X} (i : V ⟶ U) (s : A.obj (op U))
    (hs : s ∈ kernelIdeal φ (op U) ^ 2) :
    (A.map i.op).hom s ∈ kernelIdeal φ (op V) ^ 2 := by
  have h1 : Ideal.map (A.map i.op).hom (kernelIdeal φ (op U)) ≤ kernelIdeal φ (op V) :=
    Ideal.map_le_iff_le_comap.mpr (map_kernel φ i.op)
  have h2 : Ideal.map (A.map i.op).hom (kernelIdeal φ (op U) ^ 2) ≤ kernelIdeal φ (op V) ^ 2 := by
    rw [pow_two, pow_two, Ideal.map_mul]
    exact Ideal.mul_mono h1 h1
  exact h2 (Ideal.mem_map_of_mem _ hs)

/-- **Every element of the square of the kernel of the map on stalks is the germ of a section of
the square of the kernel.** -/
theorem exists_germ_eq_of_mem_stalkKernelIdeal_sq (t : ToType (A.stalk x))
    (ht : t ∈ stalkKernelIdeal φ x ^ 2) :
    ∃ (U : Opens X) (hx : x ∈ U) (s : A.obj (op U)), s ∈ kernelIdeal φ (op U) ^ 2 ∧
      (A.germ U x hx).hom s = t := by
  rw [pow_two] at ht
  refine Submodule.mul_induction_on ht ?_ ?_
  · intro m hm n hn
    obtain ⟨U₁, h₁, a₁, ha₁, rfl⟩ := exists_germ_eq_of_mem_stalkKernelIdeal φ x m hm
    obtain ⟨U₂, h₂, a₂, ha₂, rfl⟩ := exists_germ_eq_of_mem_stalkKernelIdeal φ x n hn
    have hx : x ∈ U₁ ⊓ U₂ := ⟨h₁, h₂⟩
    refine ⟨U₁ ⊓ U₂, hx,
      (A.map (homOfLE inf_le_left : U₁ ⊓ U₂ ⟶ U₁).op).hom a₁ *
        (A.map (homOfLE inf_le_right : U₁ ⊓ U₂ ⟶ U₂).op).hom a₂, ?_, ?_⟩
    · rw [pow_two]
      exact Ideal.mul_mem_mul (map_kernel φ _ ha₁) (map_kernel φ _ ha₂)
    · rw [map_mul, TopCat.Presheaf.germ_res_apply, TopCat.Presheaf.germ_res_apply]
  · rintro t₁ t₂ ⟨U₁, h₁, s₁, hs₁, e₁⟩ ⟨U₂, h₂, s₂, hs₂, e₂⟩
    have hx : x ∈ U₁ ⊓ U₂ := ⟨h₁, h₂⟩
    refine ⟨U₁ ⊓ U₂, hx,
      (A.map (homOfLE inf_le_left : U₁ ⊓ U₂ ⟶ U₁).op).hom s₁ +
        (A.map (homOfLE inf_le_right : U₁ ⊓ U₂ ⟶ U₂).op).hom s₂, ?_, ?_⟩
    · exact add_mem (map_mem_kernelIdeal_sq φ _ s₁ hs₁) (map_mem_kernelIdeal_sq φ _ s₂ hs₂)
    · rw [map_add, TopCat.Presheaf.germ_res_apply, TopCat.Presheaf.germ_res_apply, e₁, e₂]

/-! ### The comparison map is bijective -/

/-- The comparison map is surjective: every conormal class over the stalk comes from a section of
the kernel over a neighbourhood of `x`. -/
theorem conormalStalkHom_surjective : Function.Surjective (conormalStalkHom φ x) := by
  intro z
  obtain ⟨y, rfl⟩ := (stalkKernelIdeal φ x).toCotangent_surjective z
  obtain ⟨U, hU, a, ha, hay⟩ :=
    exists_germ_eq_of_mem_stalkKernelIdeal φ x (y : ToType (A.stalk x)) y.2
  refine ⟨TopCat.Presheaf.germ (C := AddCommGrpCat.{u})
    (conormalPresheafOverSource φ).presheaf U x hU
    ((kernelIdeal φ (op U)).toCotangent ⟨a, ha⟩), ?_⟩
  refine (conormalStalkHom_germ φ x U hU _).trans ?_
  exact congrArg (stalkKernelIdeal φ x).toCotangent (Subtype.ext hay)

/-- The comparison map is injective: a section of the kernel whose germ lies in `Iₓ²` already
lies in `I(V)²` over a smaller neighbourhood `V` of `x`. -/
theorem conormalStalkHom_injective : Function.Injective (conormalStalkHom φ x) := by
  refine (injective_iff_map_eq_zero (conormalStalkHom φ x)).mpr ?_
  intro ξ hξ
  obtain ⟨U, hU, c, rfl⟩ := TopCat.Presheaf.exists_germ_eq (C := AddCommGrpCat.{u})
    (conormalPresheafOverSource φ).presheaf ξ
  obtain ⟨a, rfl⟩ := (kernelIdeal φ (op U)).toCotangent_surjective c
  have hξ' := (conormalStalkHom_germ φ x U hU _).symm.trans hξ
  have hsq := (Ideal.toCotangent_eq_zero (stalkKernelIdeal φ x)
    ⟨(A.germ U x hU).hom (a : A.obj (op U)), kernelIdeal_le_comap_germ φ x U hU a.2⟩).mp hξ'
  obtain ⟨V, hV, s, hs, hsg⟩ := exists_germ_eq_of_mem_stalkKernelIdeal_sq φ x _ hsq
  obtain ⟨W, hW, iU, iV, hWe⟩ := A.germ_eq x hU hV (a : A.obj (op U)) s hsg.symm
  have hmem : (A.map iU.op).hom (a : A.obj (op U)) ∈ kernelIdeal φ (op W) ^ 2 := by
    rw [hWe]
    exact map_mem_kernelIdeal_sq φ iV s hs
  have hzero : ((conormalPresheafOverSource φ).presheaf.map iU.op).hom
      ((kernelIdeal φ (op U)).toCotangent a) = 0 :=
    (Ideal.toCotangent_eq_zero (kernelIdeal φ (op W))
      ⟨(A.map iU.op).hom (a : A.obj (op U)), map_kernel φ iU.op a.2⟩).mpr hmem
  refine (TopCat.Presheaf.germ_res_apply (C := AddCommGrpCat.{u})
    (conormalPresheafOverSource φ).presheaf iU x hW
    ((kernelIdeal φ (op U)).toCotangent a)).symm.trans ?_
  refine (congrArg (TopCat.Presheaf.germ (C := AddCommGrpCat.{u})
    (conormalPresheafOverSource φ).presheaf W x hW).hom hzero).trans ?_
  exact map_zero _

/-- The comparison map is linear over the stalk of `A`. -/
theorem conormalStalkHom_smul (r : ToType (A.stalk x))
    (ξ : ToType (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u})
      (conormalPresheafOverSource φ).presheaf x)) :
    conormalStalkHom φ x (r • ξ) = r • conormalStalkHom φ x ξ := by
  obtain ⟨Ur, hr, r₁, rfl⟩ := A.exists_germ_eq r
  obtain ⟨Uc, hc, c₁, rfl⟩ := TopCat.Presheaf.exists_germ_eq (C := AddCommGrpCat.{u})
    (conormalPresheafOverSource φ).presheaf ξ
  have hU : x ∈ Ur ⊓ Uc := ⟨hr, hc⟩
  have er := TopCat.Presheaf.germ_res_apply A
    (homOfLE (inf_le_left : Ur ⊓ Uc ≤ Ur)) x hU r₁
  have ec := TopCat.Presheaf.germ_res_apply (C := AddCommGrpCat.{u})
    (conormalPresheafOverSource φ).presheaf (homOfLE (inf_le_right : Ur ⊓ Uc ≤ Uc)) x hU c₁
  rw [← er, ← ec]
  refine (congrArg (conormalStalkHom φ x)
    (PresheafOfModules.germ_smul (conormalPresheafOverSource φ) x (Ur ⊓ Uc) hU _ _).symm).trans ?_
  refine (conormalStalkHom_germ φ x (Ur ⊓ Uc) hU _).trans ?_
  refine (germCotangentMap_smul φ x (Ur ⊓ Uc) hU _ _).trans ?_
  exact congrArg _ (conormalStalkHom_germ φ x (Ur ⊓ Uc) hU _).symm

/-- The comparison map, as a linear map over the stalk of `A`. -/
def conormalStalkLinearMap :
    ToType (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u})
        (conormalPresheafOverSource φ).presheaf x) →ₗ[ToType (A.stalk x)]
      (stalkKernelIdeal φ x).Cotangent where
  toFun := conormalStalkHom φ x
  map_add' := map_add (conormalStalkHom φ x)
  map_smul' := conormalStalkHom_smul φ x

/-- **Forming the conormal module commutes with stalks.** The stalk at `x` of the presheaf
`U ↦ I(U)/I(U)²` is the conormal module `Iₓ/Iₓ²` of the kernel of the map `Aₓ → Bₓ` on stalks. -/
def conormalPresheafStalkLinearEquiv :
    ToType (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u})
        (conormalPresheafOverSource φ).presheaf x) ≃ₗ[ToType (A.stalk x)]
      (stalkKernelIdeal φ x).Cotangent :=
  LinearEquiv.ofBijective (conormalStalkLinearMap φ x)
    ⟨conormalStalkHom_injective φ x, conormalStalkHom_surjective φ x⟩

/-- The identification `conormalPresheafStalkLinearEquiv` agrees with `conormalStalkHom`. -/
@[simp]
theorem conormalPresheafStalkLinearEquiv_apply
    (ξ : ToType (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u})
      (conormalPresheafOverSource φ).presheaf x)) :
    conormalPresheafStalkLinearEquiv φ x ξ = conormalStalkHom φ x ξ := rfl

/-- The identification carries the germ of the conormal class of a section of the kernel to the
conormal class of its germ. -/
theorem conormalPresheafStalkLinearEquiv_germ_toCotangent (U : Opens X) (hx : x ∈ U)
    (a : kernelIdeal φ (op U)) :
    conormalPresheafStalkLinearEquiv φ x (TopCat.Presheaf.germ (C := AddCommGrpCat.{u})
        (conormalPresheafOverSource φ).presheaf U x hx
        ((kernelIdeal φ (op U)).toCotangent a)) =
      (stalkKernelIdeal φ x).toCotangent
        ⟨(A.germ U x hx).hom a, kernelIdeal_le_comap_germ φ x U hx a.2⟩ :=
  conormalStalkHom_germ φ x U hx _

/-! ### The stalk of a locally surjective morphism -/

section LocallySurjective

variable [Presheaf.IsLocallySurjective (Opens.grothendieckTopology X) φ]

/-- **A locally surjective morphism of presheaves of commutative rings is surjective on
stalks.** -/
theorem stalkMap_surjective :
    Function.Surjective ((TopCat.Presheaf.stalkFunctor CommRingCat.{u} x).map φ).hom := by
  intro t
  obtain ⟨U, hxU, b, rfl⟩ := B.exists_germ_eq t
  have hcov := Presheaf.IsLocallySurjective.imageSieve_mem
    (J := Opens.grothendieckTopology X) (f := φ) b
  obtain ⟨V, g, hg, hxV⟩ := Exists.imp (fun _ h => h) (hcov x hxU)
  obtain ⟨a, ha⟩ := hg
  refine ⟨(A.germ V x hxV).hom a, ?_⟩
  refine (TopCat.Presheaf.stalkFunctor_map_germ_apply V x hxV φ a).trans ?_
  rw [ha]
  exact TopCat.Presheaf.germ_res_apply B g x hxV b

/-- **The stalk of `B` is the quotient of the stalk of `A` by the kernel `Iₓ`.** -/
def stalkQuotientRingEquiv :
    (ToType (A.stalk x) ⧸ stalkKernelIdeal φ x) ≃+* ToType (B.stalk x) :=
  RingHom.quotientKerEquivOfSurjective (stalkMap_surjective φ x)

/-- The isomorphism `stalkQuotientRingEquiv` sends the class of `y` to the image of `y` under the
map on stalks. -/
@[simp]
theorem stalkQuotientRingEquiv_mk (y : ToType (A.stalk x)) :
    stalkQuotientRingEquiv φ x (Ideal.Quotient.mk (stalkKernelIdeal φ x) y) =
      ((TopCat.Presheaf.stalkFunctor CommRingCat.{u} x).map φ).hom y := rfl

end LocallySurjective

end Presheaf

/-! ### The universe lift -/

section Lift

variable {X : TopCat.{u}} {S : (Opens X)ᵒᵖ ⥤ RingCat.{u}}

/-- The objectwise universe lift of a presheaf of modules is an isomorphism when the lift is to
the same universe. -/
def liftModulesIso (M : PresheafOfModules.{u} S) : M ≅ (liftModules.{u, u, u, u} S).obj M :=
  PresheafOfModules.isoMk
    (fun Z => (ULift.moduleEquiv (R := S.obj Z) (M := M.obj Z)).toModuleIso.symm)
    (fun {_ _} _ => by ext m; rfl)

end Lift

/-! ### The stalk of the conormal sheaf -/

section Sheaf

variable {X : TopCat.{u}} (A B : Sheaf (Opens.grothendieckTopology X) CommRingCat.{u})
  (φ : A ⟶ B) [Presheaf.IsLocallySurjective (Opens.grothendieckTopology X) φ.hom] (x : X)

/-- The conormal sheaf, regarded as a presheaf of modules over `A` by restriction of scalars
along `A ⟶ A/I ⟶ B`. -/
def conormalSheafOverSource :
    PresheafOfModules.{u} (A.obj ⋙ forget₂ CommRingCat RingCat) :=
  (PresheafOfModules.restrictScalars (toQuotientRingHom φ.hom)).obj
    ((PresheafOfModules.restrictScalars
        (quotientToRingSheaf (Opens.grothendieckTopology X) A B φ)).obj
      ((_root_.SheafOfModules.forget _).obj
        (conormalSheaf (Opens.grothendieckTopology X) A B φ)))

/-- **Sheafifying the conormal presheaf does not change its stalks.**  The universe lift is an
isomorphism and the unit of sheafification of presheaves of modules is, on underlying presheaves
of abelian groups, the unit of sheafification of presheaves of abelian groups. -/
theorem isIso_stalkFunctor_map_sheafificationUnit :
    IsIso ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
      ((PresheafOfModules.toPresheaf (quotientPresheaf φ.hom ⋙ forget₂ CommRingCat RingCat)).map
        ((liftModulesIso (conormalPresheaf φ.hom)).hom ≫
          (PresheafOfModules.sheafificationAdjunction.{u}
              (quotientToRingSheaf (Opens.grothendieckTopology X) A B φ)).unit.app
            ((liftModules.{u, u, u, u} _).obj (conormalPresheaf φ.hom))))) := by
  have h1 : IsIso ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
      ((PresheafOfModules.toPresheaf (quotientPresheaf φ.hom ⋙ forget₂ CommRingCat RingCat)).map
        (liftModulesIso (conormalPresheaf φ.hom)).hom)) := inferInstance
  have h2 : IsIso ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
      ((PresheafOfModules.toPresheaf (quotientPresheaf φ.hom ⋙ forget₂ CommRingCat RingCat)).map
        ((PresheafOfModules.sheafificationAdjunction.{u}
            (quotientToRingSheaf (Opens.grothendieckTopology X) A B φ)).unit.app
          ((liftModules.{u, u, u, u} _).obj (conormalPresheaf φ.hom))))) :=
    TopCat.Presheaf.stalkFunctor_map_unit_toSheafify_isIso x AddCommGrpCat.{u}
      ((liftModules.{u, u, u, u} (quotientPresheaf φ.hom ⋙ forget₂ CommRingCat RingCat)).obj
        (conormalPresheaf φ.hom)).presheaf
  rw [Functor.map_comp, Functor.map_comp]
  infer_instance

/-- The universe lift followed by the unit of sheafification, as a morphism of presheaves of
`A`-modules from the conormal presheaf to the conormal sheaf. -/
def toConormalSheafOverSource :
    conormalPresheafOverSource φ.hom ⟶ conormalSheafOverSource A B φ :=
  (PresheafOfModules.restrictScalars (toQuotientRingHom φ.hom)).map
    ((liftModulesIso (conormalPresheaf φ.hom)).hom ≫
      (PresheafOfModules.sheafificationAdjunction.{u}
          (quotientToRingSheaf (Opens.grothendieckTopology X) A B φ)).unit.app
        ((liftModules.{u, u, u, u} _).obj (conormalPresheaf φ.hom)))

/-- On sections the comparison morphism is the image of a conormal class under the unit of
sheafification. -/
theorem toConormalSheafOverSource_app (U : Opens X)
    (c : (conormalPresheafOverSource φ.hom).obj (op U)) :
    (toConormalSheafOverSource A B φ).app (op U) c =
      toAssociatedModule (Opens.grothendieckTopology X) A B φ (conormalPresheaf φ.hom) (op U) c :=
  rfl

/-- Restriction of scalars does not change the underlying presheaf of abelian groups, so the
comparison morphism still induces an isomorphism on stalks. -/
theorem isIso_stalkFunctor_map_toConormalSheafOverSource :
    IsIso ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
      ((PresheafOfModules.toPresheaf (A.obj ⋙ forget₂ CommRingCat RingCat)).map
        (toConormalSheafOverSource A B φ))) :=
  isIso_stalkFunctor_map_sheafificationUnit A B φ x

/-- The stalk of the conormal sheaf is a module over the stalk of `A`.  This is the module
structure of `Mathlib.Algebra.Category.ModuleCat.Stalk`, recorded at the spelling of the ring
presheaf which the restriction of scalars along `A ⟶ A/I ⟶ B` carries: instance search does not
see through the two restrictions on its own. -/
instance moduleStalkConormalSheaf :
    Module (ToType (TopCat.Presheaf.stalk A.obj x))
      (ToType (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u})
        (conormalSheaf (Opens.grothendieckTopology X) A B φ).val.presheaf x)) :=
  inferInstanceAs (Module (ToType (TopCat.Presheaf.stalk A.obj x))
    (ToType (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u})
      (conormalSheafOverSource A B φ).presheaf x)))

/-- The stalk of the conormal presheaf, identified with the stalk of the conormal sheaf. -/
def conormalSheafStalkSheafifyLinearEquiv :
    ToType (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u})
        (conormalPresheafOverSource φ.hom).presheaf x)
      ≃ₗ[ToType (TopCat.Presheaf.stalk A.obj x)]
      ToType (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u})
        (conormalSheaf (Opens.grothendieckTopology X) A B φ).val.presheaf x) :=
  Stacks.RelativeDifferentialStalk.stalkLinearEquivOfIsIso (R := A.obj) _ _
    (toConormalSheafOverSource A B φ) x
    (isIso_stalkFunctor_map_toConormalSheafOverSource A B φ x)

/-- The identification of the stalk of the conormal presheaf with the stalk of the conormal sheaf
carries the germ of a conormal class to the germ of the corresponding section of the conormal
sheaf. -/
theorem conormalSheafStalkSheafifyLinearEquiv_germ (U : Opens X) (hx : x ∈ U)
    (c : (conormalPresheafOverSource φ.hom).obj (op U)) :
    conormalSheafStalkSheafifyLinearEquiv A B φ x
        (TopCat.Presheaf.germ (C := AddCommGrpCat.{u})
          (conormalPresheafOverSource φ.hom).presheaf U x hx c) =
      TopCat.Presheaf.germ (C := AddCommGrpCat.{u})
        (conormalSheaf (Opens.grothendieckTopology X) A B φ).val.presheaf U x hx
        (toAssociatedModule (Opens.grothendieckTopology X) A B φ
          (conormalPresheaf φ.hom) (op U) c) :=
  Stacks.RelativeDifferentialStalk.stalkLinearEquivOfIsIso_germ (R := A.obj) _ _
    (toConormalSheafOverSource A B φ) x
    (isIso_stalkFunctor_map_toConormalSheafOverSource A B φ x) U hx c

/-- **The stalk of the conormal sheaf is the conormal module of the kernel on stalks.** For a
locally surjective morphism `φ : A ⟶ B` of sheaves of commutative rings with kernel `I`, the
stalk at `x` of `I/I²` is `Iₓ/Iₓ²`, where `Iₓ` is the kernel of `Aₓ → Bₓ`. -/
def conormalSheafStalkLinearEquiv :
    ToType (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u})
        (conormalSheaf (Opens.grothendieckTopology X) A B φ).val.presheaf x)
      ≃ₗ[ToType (TopCat.Presheaf.stalk A.obj x)] (stalkKernelIdeal φ.hom x).Cotangent :=
  (conormalSheafStalkSheafifyLinearEquiv A B φ x).symm.trans
    (conormalPresheafStalkLinearEquiv φ.hom x)

/-- **The identification carries conormal classes to conormal classes.** The germ at `x` of the
conormal class of a section `f` of the kernel over a neighbourhood of `x` goes to the conormal
class of the germ of `f`.  This is what makes the identification canonical. -/
theorem conormalSheafStalkLinearEquiv_germ_toAssociatedModule (U : Opens X) (hx : x ∈ U)
    (a : kernelIdeal φ.hom (op U)) :
    conormalSheafStalkLinearEquiv A B φ x
        (TopCat.Presheaf.germ (C := AddCommGrpCat.{u})
          (conormalSheaf (Opens.grothendieckTopology X) A B φ).val.presheaf U x hx
          (toAssociatedModule (Opens.grothendieckTopology X) A B φ (conormalPresheaf φ.hom) (op U)
            ((kernelIdeal φ.hom (op U)).toCotangent a))) =
      (stalkKernelIdeal φ.hom x).toCotangent
        ⟨(TopCat.Presheaf.germ A.obj U x hx).hom a,
          kernelIdeal_le_comap_germ φ.hom x U hx a.2⟩ := by
  have hE := conormalSheafStalkSheafifyLinearEquiv_germ A B φ x U hx
    ((kernelIdeal φ.hom (op U)).toCotangent a)
  show conormalPresheafStalkLinearEquiv φ.hom x
    ((conormalSheafStalkSheafifyLinearEquiv A B φ x).symm _) = _
  rw [← hE, LinearEquiv.symm_apply_apply]
  exact conormalPresheafStalkLinearEquiv_germ_toCotangent φ.hom x U hx a

/-- **The identification carries conormal classes to conormal classes**, stated for the local
sections `Stacks.Sites.Conormal.conormalClass` of the left-hand term of the conormal
sequence. -/
theorem conormalSheafStalkLinearEquiv_germ_conormalClass
    (R : Sheaf (Opens.grothendieckTopology X) CommRingCat.{u}) (a : R ⟶ A)
    (U : Opens X) (hx : x ∈ U) (y : kernelIdeal φ.hom (op U)) :
    conormalSheafStalkLinearEquiv A B φ x
        (TopCat.Presheaf.germ (C := AddCommGrpCat.{u})
          (conormalSheaf (Opens.grothendieckTopology X) A B φ).val.presheaf U x hx
          (conormalClass (Opens.grothendieckTopology X) R A B a φ (op U) y)) =
      (stalkKernelIdeal φ.hom x).toCotangent
        ⟨(TopCat.Presheaf.germ A.obj U x hx).hom y,
          kernelIdeal_le_comap_germ φ.hom x U hx y.2⟩ :=
  conormalSheafStalkLinearEquiv_germ_toAssociatedModule A B φ x U hx y

end Sheaf

end Stacks.Sites.Conormal

end

end
