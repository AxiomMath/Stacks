module

public import StacksFrontier.AlgebraicGeometry.Modules.GlueDataOfBasis
public import StacksFrontier.AlgebraicGeometry.Modules.GluedQuasicoherent

/-!
# A coherent sheaf of modules from charts compared on a basis of adapted opens

This file puts together the three preceding steps into the statement a construction by glueing
actually wants: given sheaves of modules `N i` on a scheme `Y`, quasi-coherent and of finite type
on the members `U i` of an open cover, and comparisons of their sections over the *adapted* opens
(a family of opens forming a basis of every pairwise and every triple overlap) which are
compatible with restriction and satisfy the cocycle identity there, there is a single coherent
sheaf of modules on `Y` whose sections over any open of any chart are identified with those of
that chart's sheaf, compatibly with restriction and intertwined by the given comparisons.

## Main results

* `Stacks.Modules.exists_coherent_glued_of_basisComparison`.

## Implementation notes

The family `N` is a *parameter*, deliberately: the construction instantiated at a family given by
a concrete `def` whose body is a categorical composite makes the elaborator unfold that body while
unifying the comparison data, and the application then does not elaborate at ten times the default
heartbeat allowance. Stating the result for an arbitrary family and instantiating once at the end
avoids that, and is the only reason this file exists separately from its three inputs. A caller
who does hold such a `def` should also make it `irreducible` at the point of use and supply its
defining equation as a rewrite, which is what makes the two local quasi-coherence hypotheses
dischargeable afterwards.

The last conclusion is what an independence-of-choices field of a bundled construction needs: it
says the chart identifications of the glued sheaf are intertwined by exactly the comparisons that
were supplied, so a family of identifications defined by composing one chart identification with
the given comparisons is automatically compatible.

## References

* [Stacks Project, Tag 00AM](https://stacks.math.columbia.edu/tag/00AM)
* [Stacks Project, Tag 01XZ](https://stacks.math.columbia.edu/tag/01XZ)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry Stacks.SheafOfModules

universe u v

namespace Stacks.Modules

/-- **A coherent sheaf glued from charts compared on a basis of adapted opens.** -/
public theorem exists_coherent_glued_of_basisComparison {Y : Scheme.{u}} [IsLocallyNoetherian Y]
    {ι : Type u} (U : ι → Y.Opens) (hU : iSup U = ⊤) (N : ι → Y.Modules)
    (hq : ∀ i, ((N i).restrict (U i).ι).IsQuasicoherent)
    (hf : ∀ i, ((N i).restrict (U i).ι).IsFiniteType)
    {κ : Type v} (W : κ → Y.Opens) (good : κ → ι → Prop)
    (hWU : ∀ (k : κ) (i : ι), good k i → W k ≤ U i)
    (hpair : ∀ (i j : ι) (V : Y.Opens), V ≤ U i ⊓ U j → ∀ x ∈ V,
      ∃ k, good k i ∧ good k j ∧ x ∈ W k ∧ W k ≤ V)
    (htriple : ∀ (i j m : ι) (V : Y.Opens), V ≤ U i ⊓ U j ⊓ U m → ∀ x ∈ V,
      ∃ k, good k i ∧ good k j ∧ good k m ∧ x ∈ W k ∧ W k ≤ V)
    (e : ∀ (k : κ) (i j : ι), good k i → good k j → Γ(N i, W k) ≃ₗ[Γ(Y, W k)] Γ(N j, W k))
    (hres : ∀ (k l : κ) (i j : ι) (hki : good k i) (hkj : good k j) (hli : good l i)
      (hlj : good l j) (h : W l ≤ W k) (s : Γ(N i, W k)),
      e l i j hli hlj ((N i).presheaf.map (homOfLE h).op s) =
        (N j).presheaf.map (homOfLE h).op (e k i j hki hkj s))
    (hcoc : ∀ (k : κ) (i j m : ι) (hi : good k i) (hj : good k j) (hm : good k m)
      (s : Γ(N i, W k)), e k j m hj hm (e k i j hi hj s) = e k i m hi hm s) :
    ∃ (M : Y.Modules)
      (c : ∀ (i : ι) (V : Y.Opens), V ≤ U i → (Γ(M, V) ≃ₗ[Γ(Y, V)] Γ(N i, V))),
      M.IsQuasicoherent ∧ _root_.SheafOfModules.IsCoherent M ∧
        (∀ (i : ι) (V V' : Y.Opens) (hV : V ≤ U i) (h : V' ≤ V) (s : Γ(M, V)),
          c i V' (h.trans hV) (M.presheaf.map (homOfLE h).op s) =
            (N i).presheaf.map (homOfLE h).op (c i V hV s)) ∧
        (∀ (k : κ) (i j : ι) (hki : good k i) (hkj : good k j) (s : Γ(M, W k)),
          c j (W k) (hWU k j hkj) s = e k i j hki hkj (c i (W k) (hWU k i hki) s)) := by
  obtain ⟨t, tm, tt, hagree⟩ :=
    exists_transData_of_basis U N W good hWU hpair htriple e hres hcoc
  refine ⟨(OModuleGlueData.ofModules N t tm tt).gluedModules,
    fun i V hV => (OModuleGlueData.ofModules N t tm tt).chartLinearEquiv i hV,
    isQuasicoherent_gluedModules_ofModules hU N t tm tt hq,
    isCoherent_gluedModules_ofModules hU N t tm tt hq hf,
    fun i V V' hV h s =>
      (OModuleGlueData.ofModules N t tm tt).chartLinearEquiv_restrict i hV h s,
    fun k i j hki hkj s => ?_⟩
  exact ((OModuleGlueData.ofModules N t tm tt).trans_chartLinearEquiv i j
      (hWU k i hki) (hWU k j hkj) s).symm.trans (hagree k i j hki hkj _)

end Stacks.Modules

end
