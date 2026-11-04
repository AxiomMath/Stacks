module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.AlgebraBundleStalk
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.CoherenceClosure
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.CoherentWeakSerre
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ExteriorPowerFiniteType
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FiniteTypeKernel
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorPowerCoherent
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorPowerLocalGenerators
public import StacksFrontier.LinearAlgebra.TensorAlgebra.ExteriorQuotient
import StacksCore.Tactic.StacksAttribute

/-!
# Coherence of the exterior powers of a sheaf of modules

Let `(X, 𝒪_X)` be a ringed space and `F` a coherent sheaf of `𝒪_X`-modules. Then `⋀ⁿ F` is
coherent for every `n > 0`. This is the exterior third of clause (4) of Stacks Tag 01CK; the
tensor third is `Stacks.SheafOfModules.isCoherent_tensorPower` and the symmetric third is
`Stacks.SheafOfModules.isCoherent_symmetricPower`.

The route is the quotient presentation of `⋀ⁿ F` by the degree-`n` piece of the tensor algebra.
Write `q : Tⁿ(F) ⟶ ⋀ⁿ(F)` for the sheafification of the sectionwise quotient map, which is an
epimorphism, and `K` for its kernel, so that

`0 ⟶ K ⟶ Tⁿ(F) ⟶ ⋀ⁿ(F) ⟶ 0`

is short exact. The outer two of the three facts needed are already available: `Tⁿ(F)` is
coherent for `n > 0` (clause (4) for the tensor powers), and coherent sheaves are closed under
cokernels (Tag 01BY (3)), so the clause follows as soon as `K` is coherent. Since `K` is a
subsheaf of the coherent sheaf `Tⁿ(F)`, Tag 01BY (1) reduces that to `K` being of **finite
type**, which is a local statement; and locally it is Tag 01BP, because `⋀ⁿ(F)` is of finite
presentation.

In detail: a coherent sheaf of modules is of finite presentation (Tag 01BW), so there is an open
cover over whose members `F` is presented finitely by global sections. Over such a member `U`,

* the generators of the presentation of `F|_U` give finitely many global generating sections of
  `Tⁿ(F)|_U` — `Stacks.SheafOfModules.exists_generatingSections_tensorPiece_over`, clause (1) of
  this same tag for the tensor powers; and
* the presentation of `F|_U` gives a finite presentation of `⋀ⁿ(F)|_U` by global sections —
  `Stacks.SheafOfModules.exists_isFinite_presentation_exteriorPower_over`, which is clause (3) of
  this same tag for the exterior powers and is proved from Tag 01CJ.

Those are exactly the two hypotheses of Stacks 01BP in the globally presented form
`Stacks.SheafOfModules.FiniteTypeKernel.isFiniteType_kernel_of_presentation`, applied to the
epimorphism `q|_U`, and its conclusion is that `K|_U` is of finite type. One open presents every
degree, so no further shrinking happens.

## Main definitions

* `PresheafOfModules.extQuotHom`: the sectionwise quotient `Tᵏ ⟶ ⋀ᵏ` of presheaves of modules.
* `SheafOfModules.exteriorPowerQuotHom`: **the quotient map `Tⁿ(F) ⟶ ⋀ⁿ(F)` of sheaves of
  modules**, obtained from it by sheafification, and an epimorphism.

## Main results

* `TensorAlgebra.surjective_extQuot` of
  `StacksFrontier.LinearAlgebra.TensorAlgebra.ExteriorQuotient` and
  `ExteriorAlgebra.powMapₛₗ_extQuot`: surjectivity of the sectionwise quotient map and its
  compatibility with base change, which is what makes it a morphism of presheaves of modules.
* `Stacks.SheafOfModules.isFiniteType_kernel_over_of_presentation`: Stacks 01BP read on the
  slice site at an open — the kernel of an epimorphism of sheaves of modules is of finite type
  over an open which presents the target finitely and generates the source finitely. Stated for
  an arbitrary epimorphism, with no mention of the powers.
* `Stacks.SheafOfModules.isCoherent_of_epi_of_isFiniteType_kernel_over`: **an epimorphic image
  of a coherent sheaf of modules whose kernel is of finite type on the members of an open cover
  is coherent.** This is Tag 01BY (1) and (3) in the combination this clause needs, again for an
  arbitrary epimorphism.
* `Stacks.SheafOfModules.isFiniteType_kernel_over_of_presentation_exteriorPower`: the first of
  those two specialized to the quotient map, by the two clauses of this same tag named above.
* `Stacks.SheafOfModules.isCoherent_exteriorPower`: **clause (4) of Tag 01CK for the exterior
  powers** — each exterior power of positive degree of a coherent sheaf of modules on a ringed
  space is coherent.

## Implementation notes

**Why no kernel computation, and why this is not the source's proof.** The source proves the
clause from the exact sequence `⊕_J T^{n-2}(F) ⟶ Tⁿ(F) ⟶ ⋀ⁿ(F) ⟶ 0` with `J` finite, whose
first map inserts the relators `s_i ⊗ s_i` and `s_i ⊗ s_j + s_j ⊗ s_i` of a finite generating
family `(s_i)` of `F` over an open. That sequence is exact only locally — finitely many sections
generate `F` only locally, not on sections — so the identification of the kernel has to be made
as an identity of *subsheaves*, through the sheafification unit. None of that is needed here:
Tag 01BP already says that the kernel of an epimorphism onto a finitely presented sheaf from a
sheaf with finitely many global generating sections is of finite type, and the finite
presentation of `⋀ⁿ(F)` is clause (3) of this same tag, proved from Tag 01CJ. So the only thing
this file adds to the library is the quotient map itself.

This is also why the symmetric third's route does not reappear here. That proof computes the
kernel of `Tᵏ(M) ⟶ Symᵏ(M)` algebraically — `TensorAlgebra.ker_symQuot`, the sum of the ranges
of the `k - 1` slot-wise antisymmetrisers — and the exterior analogue of that statement is
false: the kernel of `Tᵏ(M) ⟶ ⋀ᵏ(M)` is cut out by the *squares* `ι x · ι x`, and `x ↦ x ⊗ x` is
quadratic, so in characteristic two the kernel is strictly larger than the sum of the ranges of
the symmetrisers `𝟙 + τ_p`, and is not the image of any morphism of presheaves of modules built
from `F` by linear algebra. `StacksFrontier.LinearAlgebra.TensorAlgebra.ExteriorQuotient` therefore
carries the quotient map and its surjectivity and no kernel computation.

**Where the two sheafified objects are identified.** The degree-`n` piece of the tensor algebra
and the degree-`n` exterior power of a sheaf of modules are the sheafifications of the
sectionwise powers of its underlying presheaf, by `SheafOfModules.tensorPieceSheafifyIso` and
`SheafOfModules.exteriorPowerSheafifyIso`, for an arbitrary package of algebras. Those two
isomorphisms are the only point of contact between this file and the construction of the three
algebras; in particular the package's own `tensorToExterior` is never used, and neither is the
epimorphy of its degree-`n` component, which
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.UngradedRealization` records as not following from
the graded universal property.

**The quotient map is taken opaquely, and the two general lemmas never mention the powers.**
`Stacks.SheafOfModules.exists_epi_exteriorPowerQuotHom` exhibits the map existentially rather
than as a term to be unfolded, and the coherence argument runs on the variable it introduces.
Both parts of this matter. Unfolding the map would unfold the two comparison isomorphisms above
and with them the construction of the three algebras, and the elaborator does exactly that while
checking a definitional equality it could otherwise leave alone: the proof below exhausts the
heartbeat limit at `isDefEq` if the map is introduced by `set` instead, which keeps its body in
the local context. For the same reason the two general lemmas are stated for an arbitrary
epimorphism of sheaves of modules; that also gives each of the three steps its own heartbeat
budget, which the argument needs — every step crosses the two spellings of the structure sheaf of
a ringed space as a sheaf of rings at default transparency, and the cost of those checks adds up
across a single declaration.

## References

* [Stacks Project, Tag 01BP](https://stacks.math.columbia.edu/tag/01BP)
* [Stacks Project, Tag 01BW](https://stacks.math.columbia.edu/tag/01BW)
* [Stacks Project, Tag 01BY](https://stacks.math.columbia.edu/tag/01BY)
* [Stacks Project, Tag 01CJ](https://stacks.math.columbia.edu/tag/01CJ)
* [Stacks Project, Tag 01CK](https://stacks.math.columbia.edu/tag/01CK)
* [Stacks Project, Section 17.21](https://stacks.math.columbia.edu/tag/01CF)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Sheaf Opposite

universe v u w

/-! ### The sectionwise quotient map of presheaves of modules -/

namespace PresheafOfModules

section Sectionwise

variable {C : Type u} [Category.{v} C] {O : Cᵒᵖ ⥤ CommRingCat.{w}}
  (F : PresheafOfModules.{w} (O ⋙ forget₂ CommRingCat RingCat))

/-- The quotient map `TensorAlgebra.extQuot` from the sections of `tensorPow k F` over `X` onto the
sections of `extPow k F` over `X`. -/
def extQuotApp (k : ℕ) (X : Cᵒᵖ) :
    (tensorPow k F).obj X →ₗ[(O ⋙ forget₂ _ RingCat).obj X] (extPow k F).obj X :=
  TensorAlgebra.extQuot k

/-- **The sectionwise quotient `Tᵏ ⟶ ⋀ᵏ`**, as a morphism of presheaves of modules. -/
def extQuotHom (k : ℕ) : tensorPow k F ⟶ extPow k F where
  app X := ModuleCat.ofHom (extQuotApp F k X)
  naturality {_ _} f := ModuleCat.hom_ext (LinearMap.ext fun t =>
    (ExteriorAlgebra.powMapₛₗ_extQuot k ((O ⋙ forget₂ _ RingCat).map f).hom
      (F.restrictₛₗ f) t).symm)

/-- On sections over `X`, `extQuotHom F k` is the quotient map `TensorAlgebra.extQuot k`. -/
@[simp]
theorem extQuotHom_app_apply (k : ℕ) (X : Cᵒᵖ) (t : (tensorPow k F).obj X) :
    Hom.app (extQuotHom F k) X t = TensorAlgebra.extQuot k t := rfl

/-- The sectionwise quotient map `extQuotHom F k` is an epimorphism. -/
instance epi_extQuotHom (k : ℕ) : Epi (extQuotHom F k) :=
  epi_of_surjective fun _ => TensorAlgebra.surjective_extQuot k

end Sectionwise

end PresheafOfModules

/-! ### The quotient map of sheaves of modules -/

namespace SheafOfModules

section Sheafify

open PresheafOfModules

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  {Osharp : Sheaf J CommRingCat.{w}}
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify J AddCommGrpCat.{w}]
  {G : SheafOfModules.{w} (toRingCat J Osharp)}

/-- **The quotient map from the degree-`n` piece of the tensor algebra of a sheaf of modules onto
its degree-`n` exterior power**: the sheafification of the sectionwise quotient map, read through
`SheafOfModules.tensorPieceSheafifyIso` and `SheafOfModules.exteriorPowerSheafifyIso`. -/
def exteriorPowerQuotHom (A : TensorExteriorSymmetricAlgebras J G) (n : ℕ) :
    A.tensor.piece (n : ℤ) ⟶ A.exteriorPower n :=
  (tensorPieceSheafifyIso J A n).hom ≫
    (PresheafOfModules.moduleSheafification J (𝟙 Osharp.obj)).map
      (extQuotHom (valPresheaf J G) n) ≫
    (exteriorPowerSheafifyIso J A n).inv

/-- **The quotient map onto the exterior power is an epimorphism**: the sectionwise quotient map
is surjective on sections, hence an epimorphism of presheaves of modules, and sheafification is a
left adjoint. -/
instance epi_exteriorPowerQuotHom (A : TensorExteriorSymmetricAlgebras J G) (n : ℕ) :
    Epi (exteriorPowerQuotHom J A n) := by
  have hadj : (PresheafOfModules.moduleSheafification J (𝟙 Osharp.obj)).PreservesEpimorphisms :=
    Functor.preservesEpimorphisms_of_adjunction
      (PresheafOfModules.sheafificationAdjunction (toRingCatMap J (𝟙 Osharp.obj)))
  rw [exteriorPowerQuotHom]
  infer_instance

end Sheafify

end SheafOfModules

/-! ### Coherence -/

namespace Stacks.SheafOfModules

open CategoryTheory _root_.Stacks.AlgebraicGeometry TopologicalSpace _root_.Stacks.PresheafOfModules

section Quotient

variable {Y : Type u} [TopologicalSpace Y]
  {R : Sheaf (Opens.grothendieckTopology Y) RingCat.{u}}

/-- **The kernel of an epimorphism onto a sheaf of modules finitely presented over an open is of
finite type over that open**, provided the source has finitely many generating sections there.
This is Stacks 01BP, `Stacks.SheafOfModules.FiniteTypeKernel.isFiniteType_kernel_of_presentation`,
read on the slice site at `U`: restriction preserves epimorphisms and kernels. -/
theorem isFiniteType_kernel_over_of_presentation {M N : _root_.SheafOfModules.{u} R} (q : M ⟶ N)
    [Epi q] (U : Opens Y) (P : (N.over U).Presentation) [P.IsFinite]
    (σ : (M.over U).GeneratingSections) [σ.IsFiniteType] :
    ((kernel q).over U).IsFiniteType :=
  have := over_epi q U
  have := FiniteTypeKernel.isFiniteType_kernel_of_presentation P σ (q.over U)
  isFiniteType_of_iso.{u} (overKernelIso q U).symm

/-- **An epimorphic image of a coherent sheaf of modules whose kernel is of finite type on the
members of an open cover is coherent.** The kernel is a subsheaf of a coherent sheaf and locally
of finite type, hence coherent by Stacks 01BY (1) in the form
`Stacks.SheafOfModules.isCoherent_of_coversTop_of_mono`; the target is then the third term of a
short exact sequence whose first two terms are coherent, which is Stacks 01BY (3). -/
theorem isCoherent_of_epi_of_isFiniteType_kernel_over {M N : _root_.SheafOfModules.{u} R}
    (q : M ⟶ N) [Epi q] (hM : IsCoherent M) {I : Type u} (V : I → Opens Y)
    (hV : (Opens.grothendieckTopology Y).CoversTop V)
    (hft : ∀ i, ((kernel q).over (V i)).IsFiniteType) : IsCoherent N := by
  let _ : HasSheafify (Opens.grothendieckTopology Y) AddCommGrpCat.{u} := inferInstance
  let _ : (Opens.grothendieckTopology Y).WEqualsLocallyBijective AddCommGrpCat.{u} :=
    inferInstance
  have hK : IsCoherent (kernel q) :=
    isCoherent_of_coversTop_of_mono (kernel q) V hV (fun _ => M) (fun _ => hM) hft
      (fun i => (kernel.ι q).over (V i)) fun i => over_mono (kernel.ι q) (V i)
  exact isCoherent_X₃_of_shortExact
    { exact := ShortComplex.kernelSequence_exact q
      mono_f := inferInstanceAs (Mono (kernel.ι q))
      epi_g := inferInstanceAs (Epi q) } hK hM

end Quotient

variable {X : AlgebraicGeometry.RingedSpace.{u, u}}
  (F : _root_.SheafOfModules.{u} (structureSheafRing X))

/-- **The quotient map from the degree-`n` piece of the tensor algebra onto the degree-`n`
exterior power, at the spelling of the structure sheaf of rings a ringed space uses.** This is
`SheafOfModules.exteriorPowerQuotHom` together with its epimorphy; both are stated over
`CategoryTheory.Sheaf.toRingCat` of a sheaf of commutative rings, which is definitionally but not
syntactically `structureSheafRing X`, so the map and the instance are supplied
here by name rather than by synthesis — and the morphism is exhibited existentially, so that
nothing downstream can unfold it and with it the construction of the three algebras. -/
theorem exists_epi_exteriorPowerQuotHom
    (A : _root_.SheafOfModules.TensorExteriorSymmetricAlgebras
      (Opens.grothendieckTopology X.carrier) F) (n : ℕ) :
    ∃ q : A.tensor.piece (n : ℤ) ⟶ A.exteriorPower n, Epi q :=
  ⟨_root_.SheafOfModules.exteriorPowerQuotHom (Osharp := X.sheaf)
      (Opens.grothendieckTopology X.carrier) A n,
    _root_.SheafOfModules.epi_exteriorPowerQuotHom (Osharp := X.sheaf)
      (Opens.grothendieckTopology X.carrier) A n⟩

/-- **The kernel of the quotient map `Tⁿ(F) ⟶ ⋀ⁿ(F)` is of finite type over an open which
presents `F` finitely.** The presentation of `F|_U` gives finitely many generating sections of
`Tⁿ(F)|_U` and a finite presentation of `⋀ⁿ(F)|_U`, which are the two hypotheses of Stacks
01BP. -/
theorem isFiniteType_kernel_over_of_presentation_exteriorPower
    (A : _root_.SheafOfModules.TensorExteriorSymmetricAlgebras
      (Opens.grothendieckTopology X.carrier) F) (n : ℕ) (U : Opens X.carrier)
    (p : (F.over U).Presentation) [hp : p.IsFinite]
    {q : A.tensor.piece (n : ℤ) ⟶ A.exteriorPower n} (hq : Epi q) :
    ((kernel q).over U).IsFiniteType := by
  have := hq
  obtain ⟨r, hr⟩ := exists_isFinite_presentation_exteriorPower_over U F A p n (hp := hp)
  obtain ⟨τ, hτ⟩ := exists_generatingSections_tensorPiece_over F A U p.generators n
  have hrfin : r.IsFinite := hr
  have hτfin : τ.IsFiniteType := ⟨hτ hp.isFiniteType_generators.finite⟩
  exact isFiniteType_kernel_over_of_presentation q U r τ

/-- **Each exterior power of positive degree of a coherent sheaf of modules on a ringed space is
coherent.** This is clause (4) of [Stacks, Tag 01CK] for the exterior powers. The kernel `K` of
the quotient map `Tⁿ(F) ⟶ ⋀ⁿ(F)` is of finite type over each member of a cover presenting `F`
finitely, by Tag 01BP; hence coherent by Tag 01BY (1), since it is a subsheaf of the coherent
sheaf `Tⁿ(F)`; hence `⋀ⁿ(F)` is coherent by Tag 01BY (3). -/
@[stacks 01CK "exterior powers of a coherent module, in positive degree"]
theorem isCoherent_exteriorPower [_root_.SheafOfModules.IsCoherent F]
    (A : _root_.SheafOfModules.TensorExteriorSymmetricAlgebras
      (Opens.grothendieckTopology X.carrier) F) (n : ℕ) (hn : 0 < n) :
    _root_.SheafOfModules.IsCoherent (A.exteriorPower n) := by
  have hT : IsCoherent (A.tensor.piece (n : ℤ)) :=
    (TensorOver.isCoherent_iff _).1 (isCoherent_tensorPower F A n hn)
  have hFP : F.IsFinitePresentation := isFinitePresentation_of_isCoherent F
  obtain ⟨c, hc⟩ :=
    _root_.SheafOfModules.IsFinitePresentation.exists_quasicoherentData.{u, u, u} F
  obtain ⟨q, hq⟩ := exists_epi_exteriorPowerQuotHom F A n
  have := hq
  exact (TensorOver.isCoherent_iff _).2
    (isCoherent_of_epi_of_isFiniteType_kernel_over q hT c.X c.coversTop fun i =>
      isFiniteType_kernel_over_of_presentation_exteriorPower F A n (c.X i) (c.presentation i)
        (hp := hc.isFinite_presentation i) hq)

end Stacks.SheafOfModules

end
